open import Relation.Binary
open import Level

module Experiments.Infer {c ℓ₁ ℓ₂}(PO : Preorder c ℓ₁ ℓ₂) where

open Preorder PO renaming (_∼_ to _⊑_)

record IsIncluded (W W' : Carrier) : Set ℓ₂ where
  field
    is-included : W ⊑ W'

record IsIncludedOnce (W W' : Carrier) : Set ℓ₂ where
  field
    is-included-once : W ⊑ W'

instance
  is-included-refl : ∀ {W} → IsIncluded W W
  is-included-refl = record { is-included = refl }

  is-included-step : ∀ {W W' W''} ⦃ p : IsIncludedOnce W W' ⦄ ⦃ q : IsIncluded W' W'' ⦄ → IsIncluded W W''
  is-included-step
    {{p = record { is-included-once = p }}}
    {{record { is-included = q }}} = record { is-included = trans p q }

-- typeclass for world-indexed things that support weakening
record Weakenable {i}(I : Carrier → Set i) : Set (i ⊔ ℓ₂ ⊔ c) where
  field
    weaken : ∀ {W W'} → W ⊑ W' → I W → I W'

  wk     : ∀ {W W'} → I W → ⦃ p : IsIncluded W W' ⦄ → I W'
  wk x ⦃ record { is-included = p } ⦄ = weaken p x

ISet = Carrier → Set

module Monad
  (M    : ISet → ISet)
  (ret  : ∀ {P : ISet}{c} → P c → M P c)
  (bind : ∀ {P Q : ISet}{c} → (∀ {c'} ⦃ sub : IsIncludedOnce c c' ⦄ → P c' → M Q c') → M P c → M Q c)
  (V    : ISet)
  (wV   : Weakenable V)
  (get  : ∀ {c} → M V c)
  (App  : ∀ {c} → V c → V c → V c)
  where

  instance
    weakenable-val = wV

  open Weakenable ⦃...⦄

  test : ∀ {c} → M V c
  test = bind (λ x → bind (λ y → ret (App (wk x) (wk y))) get) get
