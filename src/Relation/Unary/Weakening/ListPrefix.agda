open import Agda.Primitive
import Data.List as List
open import Data.List.Most
open import Data.List.All as List∀
open import Function
open import Level

module Relation.Unary.Weakening.ListPrefix {a} {A : Set a} where

open import Relation.Unary.Weakening (List A)
                                      _⊑_
                                      ⊑-refl
                                      ⊑-trans public

open Wk ⦃ ... ⦄ public

instance
  any-weakenable : ∀ {x : A} → Wk (λ xs → x ∈ xs)
  any-weakenable = record { wk = λ ext l → ∈-⊒ l ext }

  all-weakenable : ∀ {j}{B : Set j}{xs : List B}
                     {k}{C : B → List A → Set k}( wₐ : ∀ x → Wk (C x) ) →
                     Wk (λ ys → All (λ x → C x ys) xs)
  all-weakenable wₐ = record {
    wk = λ ext v → List∀.map (λ {a} y → Wk.wk (wₐ a) ext y) v }

  const-weakenable : ∀ {j i}{I : Set i}{A : Set j} → Wk (λ _ → A)
  const-weakenable = record { wk = λ ext c → c }

  list-weakenable : ∀ {b}{B : List A → Set b}
                    ⦃ wb : Wk B ⦄ → Wk (λ W → List (B W))
  list-weakenable ⦃ wₐ ⦄ = record {wk = λ ext v → List.map (wk ext) v }


-- Nicer syntax for transitivity of prefixes:
infixl 30 _⊚_
_⊚_ : ∀ {W W' W'' : List A} → W' ⊒ W → W'' ⊒ W' → W'' ⊒ W
_⊚_ co₁ co₂ = ⊑-trans co₁ co₂

{-
  Another common construction is that of products of weakenable
  predicates.  Section 3.4 defines this type, which corresponds to
  `_∩_` from the Agda Standard Library:
-}
open import Relation.Unary
open import Data.Product
_⊗_ : ∀ {i j}(P : List A → Set i)(Q : List A → Set j)(a : List A) → Set (i ⊔ j)
_⊗_ = _∩_

-- We prove that when `_⊗_` is a product of two weakenable predicates,
-- then `_⊗_` is an instance of `Weakenable`:
instance
  weaken-pair : ∀ {i j}{P : List A → Set i}{Q : List A → Set j}
                  ⦃ wp : Wk P ⦄ ⦃ wq : Wk Q ⦄ →
                  Wk (P ⊗ Q)
  weaken-pair = record { wk = λ{ ext (x , y) → (wk ext x , wk ext y) } }
