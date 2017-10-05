open import Agda.Primitive
open import Data.List.Most
open import Data.List.All as List∀
open import Function
open import Level

module Common.Weakening  where

record Weakenable {i j}{A : Set i}(p : List A → Set j) : Set (i ⊔ j) where
  field wk : ∀ {w w'} → w ⊑ w' → p w → p w'

-- Some weakening functions for common structures

instance
  any-weakenable : ∀ {i}{A : Set i}{x : A} → Weakenable (λ xs → x ∈ xs)
  any-weakenable = record { wk = λ ext l → ∈-⊒ l ext }

  all-weakenable : ∀ {i}{A : Set i}{j}{B : Set j}{xs : List B}
                     {k}{C : B → List A → Set k}( wₐ : ∀ x → Weakenable (C x) ) →
                     Weakenable (λ ys → All (λ x → C x ys) xs)
  all-weakenable wₐ = record {
    wk = λ ext v → List∀.map (λ {a} y → Weakenable.wk (wₐ a) ext y) v }

  const-weakenable : ∀ {j i}{I : Set i}{A : Set j} → Weakenable {A = I} (λ _ → A)
  const-weakenable = record { wk = λ ext c → c }

-- nicer syntax for transitivity
infixl 30 _⊚_
_⊚_ : ∀ {i}{A : Set i}{W W' W'' : List A} → W' ⊒ W → W'' ⊒ W' → W'' ⊒ W
_⊚_ co₁ co₂ = ⊑-trans co₁ co₂

-- Product on of indexed predicates
open import Relation.Unary
open import Data.Product
_⊗_ : ∀ {a}{i j}{W : Set a}(p : W → Set i)(q : W → Set j)(w : W) → Set (i ⊔ j)
_⊗_ = _∩_

open Weakenable ⦃...⦄ public

instance
  weaken-pair : ∀ {a}{A : Set a}{i j}{p : List A → Set i}{q : List A → Set j}
                  ⦃ wp : Weakenable p ⦄ ⦃ wq : Weakenable q ⦄ →
                  Weakenable (p ⊗ q)
  weaken-pair = record { wk = λ{ ext (x , y) → (wk ext x , wk ext y) } }
