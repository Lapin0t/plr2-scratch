module polyfun where

open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (subst to subst≡)

open import Data.Product using (Σ ; Σ-syntax ; proj₁ ; proj₂ ; _×_ ; _,_ )
open import Data.Nat using (ℕ ; _+_) renaming (zero to ze ; suc to su)
open import Data.Fin using (splitAt) renaming (Fin to fin ; zero to ze ; suc to su)
open import Data.List using ([] ; _∷_) renaming (List to list)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)

_⇒_ : ∀ {I : Set} → (I → Set) → (I → Set) → Set
X ⇒ Y = ∀ {i} → X i → Y i

data F₀ : Set where
data F₁ : Set where ⓪ : F₁
data F₂ : Set where ⓪ ① : F₂
data F₃ : Set where ⓪ ① ② : F₃
data F₄ : Set where ⓪ ① ② ③ : F₄

{-
data hvec : list Set → Set where
  [] : hvec []
  _∷_ : ∀ {T U} (x : T) (xs : hvec U) → hvec (T ∷ U)

collect : ∀ {ℓ} {A : Set ℓ} {n} → (fin n → A) → list A
collect {n = ze}   xs = []
collect {n = su n} xs = xs ze ∷ collect (xs ∘ su)

hvec′ : (n : ℕ) → (fin n → Set) → Set
hvec′ n T = hvec (collect T)

mk-hvec′ : ∀ {n} {T : fin n → Set} (xs : ∀ i → T i) → hvec′ n T
mk-hvec′ {n = ze}   xs = []
mk-hvec′ {n = su n} xs = xs ze ∷ mk-hvec′ (xs ∘ su)

hget′ : ∀ {n} {T : fin n → Set} (i : fin n) → hvec′ n T → T i
hget′ ze     (x ∷ _)  = x
hget′ (su i) (_ ∷ xs) = hget′ i xs

hfoldr′ : ∀ {n} {T : fin n → Set} (A : Set)
         → A → (∀ {i} → T i → A → A) → hvec′ n T → A
hfoldr′ {n = ze} A a f [] = a
hfoldr′ {n = su n} A a f (x ∷ xs) = f x (hfoldr′ A a f xs)

hmap′ : ∀ {n} {S T : fin n → Set} → (S ⇒ T) → hvec′ n S → hvec′ n T
hmap′ {n = ze} f [] = []
hmap′ {n = su n} f (x ∷ xs) = f x ∷ hmap′ f xs
-}

record poly′ (I : Set) : Set₁ where
  field
    sh : Set
    po : sh → Set
    nx : (s : sh) → po s → I
open poly′ public

record _⇒′ₚ_ {I} (P Q : poly′ I) : Set where
  field
    sh⇒ : P .sh → Q .sh
    po⇐ : (s : P .sh) → Q .po (sh⇒ s) → P .po s
    coh : ∀ {s : P .sh} p → P .nx s (po⇐ s p) ≡ Q .nx _ p
open _⇒′ₚ_ public


module _ {I : Set} where

  ⟦_⟧′ₚ : poly′ I → (I → Set) → Set
  ⟦ P ⟧′ₚ X = Σ[ s ∈ P .sh ] ((p : P .po s) → X (P .nx s p))

  ⟦_⟧′⇒ₚ : ∀ {P Q : poly′ I} (m : P ⇒′ₚ Q) {X} → ⟦ P ⟧′ₚ X → ⟦ Q ⟧′ₚ X
  ⟦ m ⟧′⇒ₚ {X} (s , k) =
    m .sh⇒ s ,  λ p → subst≡ X (m .coh p) (k (m .po⇐ s p))

  fmap′ₚ : ∀ {P X Y} → X ⇒ Y → ⟦ P ⟧′ₚ X → ⟦ P ⟧′ₚ Y
  fmap′ₚ f (s , k) = s , f ∘ k 


  _+′ₚ_ : poly′ I → poly′ I → poly′ I
  (P +′ₚ Q) .sh = P .sh ⊎ Q .sh
  (P +′ₚ Q) .po (inj₁ s) = P .po s
  (P +′ₚ Q) .po (inj₂ s) = Q .po s
  (P +′ₚ Q) .nx (inj₁ s) p = P .nx s p
  (P +′ₚ Q) .nx (inj₂ s) p = Q .nx s p

  _×′ₚ_ : poly′ I → poly′ I → poly′ I
  (P ×′ₚ Q) .sh = P .sh × Q .sh
  (P ×′ₚ Q) .po (r , s) = P .po r ⊎ Q .po s
  (P ×′ₚ Q) .nx (r , s) (inj₁ p) = P .nx r p
  (P ×′ₚ Q) .nx (r , s) (inj₂ p) = Q .nx s p

  Π′ : (A : Set) → (A → poly′ I) → poly′ I
  Π′ A P .sh = (a : A) → P a .sh
  Π′ A P .po s = Σ[ a ∈ A ] (P a .po (s a))
  Π′ A P .nx s (a , p) = P a .nx (s a) p

  Κ′ : Set → poly′ I
  Κ′ A .sh = A
  Κ′ A .po _ = F₀
  Κ′ A .nx s ()

  _>>=′ₚ_ : (P : poly′ I) → (P .sh → poly′ I) → poly′ I
  (P >>=′ₚ Q) .sh = {!!}
  (P >>=′ₚ Q) .po s = {!!}
  (P >>=′ₚ Q) .nx s p = {!!}
  --(P >>=′ₚ Q) .sh =  ⟦ P ⟧′ₚ (sh ∘ Q)
  --(P >>=′ₚ Q) .po (s , k) = Σ[ p ∈ P .po s ] Q _ .po (k p)
  --(P >>=′ₚ Q) .nx (s , k) (p , q) = Q _ .nx (k p) q

poly : (I J : Set) → Set₁
poly I J = I → poly′ J

module _ {I J : Set} where

  _⇒ₚ_ : poly I J → poly I J → Set
  P ⇒ₚ Q = ∀ {i} → P i ⇒′ₚ Q i

  ⟦_⟧ₚ : poly I J → (J → Set) → (I → Set)
  ⟦ P ⟧ₚ X i = ⟦ P i ⟧′ₚ X

  ⟦_⟧⇒ₚ : ∀ {P Q : poly I J} (m : P ⇒ₚ Q) {X} → ⟦ P ⟧ₚ X ⇒ ⟦ Q ⟧ₚ X
  ⟦ m ⟧⇒ₚ {X} x = ⟦ m ⟧′⇒ₚ {X} x
  
  fmapₚ : ∀ {P X Y} → X ⇒ Y → ⟦ P ⟧ₚ X ⇒ ⟦ P ⟧ₚ Y
  fmapₚ {X = X} m x = fmap′ₚ {X = X} m x

  _+ₚ_ : poly I J → poly I J → poly I J
  (P +ₚ Q) i = P i +′ₚ Q i

  _×ₚ_ : poly I J → poly I J → poly I J
  (P ×ₚ Q) i = P i ×′ₚ Q i
  
  Κ : (I → Set) → poly I J
  Κ X i = Κ′ (X i)

  _⊙_ : ∀ {K} → poly J K → poly I J → poly I K
  (Q ⊙ P) i = {!!} --P i >>=′ₚ λ j → Π′ {!!} {!!}


  {-



  {-_⊙ₚ_ : poly I → poly I → poly I
  (P ⊙ₚ Q) .sh = ⟦ Q ⟧ₚ (P .sh)
  (P ⊙ₚ Q) .po (s , k) = aux s k
  (P ⊙ₚ Q) .nx (s , k) n = {!!}-}
  --with fin (hfoldr′ ℕ ze (λ i → P .po i +_) k) | Q .po s | k | n
  --... | a | b | c | d = {!!}

-}
