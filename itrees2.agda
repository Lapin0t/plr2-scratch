module itrees2 where

open import Size

open import polyfun

data itreeF {I} (T : (I → Set) → I → Set) (E : poly I) (X : I → Set) (i : I) : Set where
  retF : X i → itreeF T E X i
  tauF : T X i → itreeF T E X i
  visF : (s : E .sh i) → hvec′ (E .po s) (T X ∘ E .nx s) → itreeF T E X i

record itree {I} (E : poly I) (ℓ : Size) (X : I → Set) (i : I) : Set where
  coinductive
  field
    obs : ∀ {ℓ′ : Size< ℓ} → itreeF (itree E ℓ′) E X i
