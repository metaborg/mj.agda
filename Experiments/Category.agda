open import Relation.Binary hiding (_⇒_)

module Experiments.Category {ℓ₁ ℓ₂ ℓ₃} (APO : Preorder ℓ₁ ℓ₂ ℓ₃) where

open import Level
open Preorder APO

record IsMP {ℓ}(P : Carrier → Set ℓ) : Set (ℓ ⊔ ℓ₁ ⊔ ℓ₃) where
  field
    monotone : ∀ {c c'} → c ∼ c' → P c → P c'

-- monotone predicates over a fixed carrier
record MP ℓ : Set (suc ℓ ⊔ ℓ₁ ⊔ ℓ₃) where
  constructor mp
  field
    pred  : Carrier → Set ℓ
    is-mp : IsMP pred

  open IsMP is-mp public

-- application
_·_ : ∀ {ℓ} → MP ℓ → Carrier → Set _
(mp pred _) · c = pred c

-- product
open import Data.Product
_⊗_ : ∀ {ℓ₁ ℓ₂} → MP ℓ₁ → MP ℓ₂ → MP (ℓ₁ ⊔ ℓ₂)
P ⊗ Q = mp
    (λ c → (P · c) × (Q · c))
    (record {
      monotone = λ{ c~c' (p , q) →
          MP.monotone P c~c' p
        , MP.monotone Q c~c' q
      }
    })

-- monotone-predicate transformers are the morphisms of this category
_⇒_ : (ℓ₁ ℓ₂ : Level) → Set _
ℓ₁ ⇒ ℓ₂ = MP ℓ₁ → MP ℓ₂

MPT = zero ⇒ zero
