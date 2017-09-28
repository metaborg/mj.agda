open import Agda.Primitive
open import Data.List.Most
open import Data.List.All as List∀
open import Function

module Common.Weakening {i}{A : Set i} where

record Weakenable {j}(p : List A → Set j) : Set (i ⊔ j) where
  field wk : ∀ {w w'} → w ⊑ w' → p w → p w'

-- Some weakening functions for common structures

instance
  any-weakenable : ∀ {x : A} → Weakenable (λ xs → x ∈ xs)
  any-weakenable = record { wk = λ ext l → ∈-⊒ l ext }

  all-weakenable : ∀ {j}{B : Set j}{xs : List B}
                     {k}{C : B → List A → Set k}( wₐ : ∀ x → Weakenable (C x) ) →
                     Weakenable (λ ys → All (λ x → C x ys) xs)
  all-weakenable wₐ = record {
    wk = λ ext v → List∀.map (λ {a} y → Weakenable.wk (wₐ a) ext y) v }

  const-weakenable : ∀ {i}{A : Set i} → Weakenable (λ _ → A)
  const-weakenable = record { wk = λ ext c → c }

-- nicer syntax for transitivity
infixl 30 _⊚_
_⊚_ : ∀ {W W' W'' : List A} → W' ⊒ W → W'' ⊒ W' → W'' ⊒ W
_⊚_ co₁ co₂ = ⊑-trans co₁ co₂
