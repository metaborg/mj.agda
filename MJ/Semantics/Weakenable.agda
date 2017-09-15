module MJ.Semantics.Weakenable {c} where

open import Prelude
open import MJ.Types
open import Data.List.Prefix
open import Data.List
open import Data.List.All as List∀
open import Data.List.Any.Membership.Propositional

record IsIncluded (W W' : World c) : Set where
  field
    is-included : W ⊑ W'
record IsIncludedOnce (W W' : World c) : Set where
  field
    is-included-once : W ⊑ W'

instance
  is-included-refl : ∀ {W} → IsIncluded W W
  is-included-refl = record { is-included = ⊑-refl }

  is-included-step : ∀ {W W' W''} ⦃ p : IsIncludedOnce W W' ⦄ ⦃ q : IsIncluded W' W'' ⦄ → IsIncluded W W''
  is-included-step
    {{p = record { is-included-once = p }}}
    {{record { is-included = q }}} = record { is-included = ⊑-trans p q }

-- typeclass for world-indexed things that support weakening
record Weakenable {i}(I : World c → Set i) : Set i where
  field
    weaken : ∀ {W W'} → W' ⊒ W → I W → I W'

  wk     : ∀ {W W'} → I W → ⦃ p : IsIncluded W W' ⦄ → I W'
  wk x ⦃ record { is-included = p } ⦄ = weaken p x

-- nicer syntax for transitivity
infixl 30 _⊚_
_⊚_ : ∀ {W W' W'' : World c} → W' ⊒ W → W'' ⊒ W' → W'' ⊒ W
_⊚_ co₁ co₂ = ⊑-trans co₁ co₂

instance
  any-weakenable : ∀ {a} → Weakenable (λ W → a ∈ W)
  any-weakenable = record { weaken = λ ext r → ∈-⊒ r ext }

  all-weakenable : ∀ {B : Set}{xs : List B}
                        {A : B → World c → Set}⦃ wₐ : ∀ {x} → Weakenable (A x) ⦄ →
                        Weakenable (λ W → All (λ x → A x W) xs)
  all-weakenable ⦃ wₐ ⦄ = record {
    weaken = λ ext v → List∀.map (λ y → Weakenable.weaken wₐ ext y) v }
