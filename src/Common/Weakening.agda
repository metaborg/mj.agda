open import Agda.Primitive
open import Data.List.Most
open import Data.List.All as List∀

module Common.Weakening {i}{A : Set i} where

record Weakenable {j}(p : List A → Set j) : Set (i ⊔ j) where
  field weaken : ∀ {w w'} → w ⊑ w' → p w → p w'

-- Some weakening functions for common structures

instance
  any-weakenable : ∀ {x : A} → Weakenable (λ xs → x ∈ xs)
  any-weakenable = record { weaken = λ ext l → ∈-⊒ l ext }

  all-weakenable : ∀ {j}{B : Set j}{xs : List B}
                     {k}{C : B → List A → Set k}( wₐ : ∀ x → Weakenable (C x) ) →
                     Weakenable (λ ys → All (λ x → C x ys) xs)
  all-weakenable wₐ = record {
    weaken = λ ext v → List∀.map (λ {a} y → Weakenable.weaken (wₐ a) ext y) v }

