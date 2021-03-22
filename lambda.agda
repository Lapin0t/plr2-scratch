module lambda where

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Fin using (Fin ; zero ; suc)

open import itrees

data T₀ : Set where
data T₁ : Set where t₁₀ : T₁
data T₂ : Set where t₂₀ t₂₁ : T₂
data T₃ : Set where t₃₀ t₃₁ t₃₂ : T₃

data term : Set where
  var : ℕ → term
  lam : term → term
  app : term → term → term

data termR : Set where
  varR : ℕ → termR
  lamR : termR
  appR : termR
    
termE : evt
termE .req = termR
termE .ans (varR _) = T₀
termE .ans lamR     = T₁
termE .ans appR     = T₂

termT : Size → Set
termT i = itree termE i T₀

varT : ℕ → termT i
varT i .obs = visF (varR i , λ ())

lamT : termT i → termT i
lamT u .obs = visF (lamR , λ { t₁₀ → u })

appT : termT i → termT i → termT i
appT u v .obs = visF (appR , λ { t₂₀ → u ; t₂₁ → v })

inj-term : term → termT i
inj-term (var i)   = varT i
inj-term (lam u)   = lamT (inj-term u)
inj-term (app u v) = appT (inj-term u) (inj-term v)

rename : (ℕ → ℕ) → termT i → termT i
rename f u .obs with u .obs
... | tauF t            = tauF (rename f t)
... | visF (varR i , k) = visF (varR (f i) , λ ())
... | visF (lamR   , k) = visF (lamR , λ { t₁₀ → rename (λ { zero → zero
                                                          ; (suc n) → suc (f n)})
                                                        (k t₁₀) })
... | visF (appR   , k) = visF (appR , λ { t₂₀ → rename f (k t₂₀)
                                         ; t₂₁ → rename f (k t₂₁)})

subst : (ℕ → termT i) → termT i → termT i
subst f u .obs with u .obs
... | tauF t            = tauF (subst f t)
... | visF (varR i , k) = f i .obs
... | visF (lamR   , k) = visF (lamR , λ { t₁₀ → subst (λ { zero → varT zero
                                                           ; (suc n) → rename suc (f n)}) (k t₁₀)})
... | visF (appR   , k) = visF (appR , λ { t₂₀ → subst f (k t₂₀) ; t₂₁ → subst f (k t₂₁)})

data normR : Set where
  lamR : normR
  rdxR : ℕ → ℕ → normR

normE : evt
normE .req = normR
normE .ans lamR       = T₁
normE .ans (rdxR _ n) = Fin n

normT : Size → Set
normT i = itree normE i T₀

norm2term : normT i → termT i
norm2term u .obs with u .obs
... | tauF t = tauF (norm2term t)
... | visF (lamR     , k) = visF (lamR , λ { t₁₀ → norm2term (k t₁₀)})
... | visF (rdxR i j , k) = tauF (spine j (varT i) k)
  where spine : ∀ {i} (n : ℕ) → termT i → (Fin n → normT i) → termT i
        spine zero a f = a 
        spine (suc n) a f = appT (spine n a (f ∘ suc)) (norm2term (f zero))

eval : termT i → normT i
eval-app : normT i → normT i → normT i

eval u .obs with u .obs
... | tauF t = tauF (eval t)
... | visF (varR i , k) = visF (rdxR i zero , λ ())
... | visF (lamR   , k) = visF (lamR , λ { t₁₀ → eval (k t₁₀) } )
... | visF (appR   , k) = tauF (eval-app (eval (k t₂₀)) (eval (k t₂₀)))

eval-app u v .obs with u .obs
... | tauF t = tauF (eval-app t v)
... | visF (lamR     , k) = tauF (eval (subst (λ { zero → norm2term v
                                                 ; (suc n) → varT n})
                                              (norm2term (k t₁₀))))
... | visF (rdxR i j , k) = visF (rdxR i (suc j) , λ {zero → v ; (suc n) → k n})
