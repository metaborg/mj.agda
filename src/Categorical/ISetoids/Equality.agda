module Categorical.ISetoids.Equality where

open import Categories.Support.Equivalence

open Setoid

_[_≈_] : ∀ {s₁ s₂} (S : Setoid s₁ s₂) → Carrier S → Carrier S → Set _
_[_≈_] = Setoid._≈_

