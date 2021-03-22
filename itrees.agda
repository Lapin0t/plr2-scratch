module itrees where

open import Size public
open import Function using (_∘_) public
open import Data.Product using (Σ ; Σ-syntax ; proj₁ ; proj₂ ; _×_ ; _,_ ) public
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂) public

-- ==========================================
-- event descriptions: families and utilities
-- ==========================================

record evt : Set₁ where
  field
    req : Set        -- type of requests
    ans : req → Set  -- types of answers
open evt public

-- 'fiber F X' encodes the set of requests that have X as answer type
-- (this is the fam2pow translation)
data fiber (F : evt) : Set → Set where
  fib : (e : F .req) → fiber F (F .ans e)

_⇒_ : (Set → Set) → (Set → Set) → Set₁
A ⇒ B = ∀ {X} → A X → B X

-- note how this is in 'Set' vs 'Set₁' for '_⇒_'; this is one of the
-- advantages of families over power-sets: no high-order quantification
_ₑ⇒_ : evt → (Set → Set) → Set
F ₑ⇒ A = (e : F .req) → A (F .ans e)

_ₑ⇒ₑ_ : evt → evt → Set
F ₑ⇒ₑ G = F ₑ⇒ fiber G

fiber-ind : ∀ {F} A → F ₑ⇒ A → fiber F ⇒ A
fiber-ind _ h (fib e) = h e

_+ₑ_ : evt → evt → evt
(F +ₑ G) .req = F .req ⊎ G .req
(F +ₑ G) .ans (inj₁ e) = F .ans e
(F +ₑ G) .ans (inj₂ e) = G .ans e

_×ₑ_ : evt → evt → evt
(F ×ₑ G) .req = F .req × G .req
(F ×ₑ G) .ans (q₀ , q₁) = F .ans q₀ ⊎ G .ans q₁

-- interpretation of 'evt' as a familial endofunctor on Set;
-- itree will be the free (iterative) monad over
-- this functor
⟦_⟧ₑ : evt → Set → Set
⟦ F ⟧ₑ X = Σ[ q ∈ F .req ] (F .ans q → X)

variable
  {E F} : evt
  {X Y Z} : Set
  {i} : Size

-- functor action of ⟦ E ⟧ₑ
fmapₑ : (X → Y) → ⟦ E ⟧ₑ X → ⟦ E ⟧ₑ Y
fmapₑ f (e , k) = e , f ∘ k

-- functor action of ⟦_⟧ₑ as a functor 'Evt → Fct(Set, Set)'
mapₑ : E ₑ⇒ₑ F → ⟦ E ⟧ₑ ⇒ ⟦ F ⟧ₑ
mapₑ {E} m (r , k) with E .ans r | m r
... | _ | fib e = e , k

data itreeF (T : Set → Set) (E : evt) (X : Set) : Set where
  retF : (x : X) → itreeF T E X
  tauF : (t : T X) → itreeF T E X
  visF : ⟦ E ⟧ₑ (T X) → itreeF T E X

record itree (E : evt) (i : Size) (X : Set) : Set where
  coinductive
  field
    obs : ∀ {j : Size< i} → itreeF (itree E j) E X
open itree public

itree' : evt → Size → Set → Set
itree' E i X = itreeF (itree E i) E X

ret : X → itree E i X
ret x .obs = retF x

tau : (∀ {j : Size< i} → itree E j X) → itree E i X
tau t .obs = tauF t 

vis : (e : E .req) → (∀ {j : Size< i} → E .ans e → itree E j X) → itree E i X
vis e k .obs = visF (e , k)

bind : itree E i X → (X → itree E i Y) → itree E i Y
bind u f .obs with u .obs
... | retF x       = f x .obs
... | tauF t       = tauF (bind t f)
... | visF (e , k) = visF (e , λ r → bind (k r) f)

map : (X → Y) → itree E i X → itree E i Y
map f u = bind u (ret ∘ f) 

trigger : E ₑ⇒ itree E i
trigger e = vis e ret

spin : itree E i X
spin .obs = tauF spin

forever : itree E i X → itree E i Y
forever u = bind u λ { _ .obs → tauF (forever u) }

kcomp : (X → itree E i Y) → (Y → itree E i Z) → X → itree E i Z
kcomp f g u = bind (f u) g

iter : (X → itree E i (X ⊎ Y)) → X → itree E i Y
iter step x = bind (step x) λ { (inj₁ x) .obs → tauF (iter step x)
                              ; (inj₂ y) .obs → retF y }


mrec′ : (∀ {i} → E ₑ⇒ itree (E +ₑ F) i) → itree (E +ₑ F) i ⇒ itree F i
mrec′ h u .obs with u .obs
... | retF x   = retF x
... | tauF t   = tauF (mrec′ h t)
... | visF (inj₁ x , k) = tauF (bind (mrec′ h (h x)) (mrec′ h ∘ k))
... | visF (inj₂ y , k) = visF (y , mrec′ h ∘ k)

mrec : (∀ {i} → E ₑ⇒ itree (E +ₑ F) i) → E ₑ⇒ itree F i
mrec h e = mrec′ h (h e)

efold : (∀ {i} → ⟦ E ⟧ₑ (itree F i X) → itree F i X) → itree E i X → itree F i X
efold h u .obs with u .obs
... | retF x       = retF x
... | tauF t       = tauF (efold h t)
... | visF (e , k) = tauF (h (e , efold h ∘ k))
