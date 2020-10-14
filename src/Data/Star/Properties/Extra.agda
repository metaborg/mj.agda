module Data.Star.Properties.Extra where

open import Relation.Binary.Core
open import Data.Star

module _ {i}{I : Set i}{r}{R : Rel I r} where
  _◅◅-ε : ∀ {i j} → (xs : Star R i j) → xs ◅◅ ε ≡ xs
  ε ◅◅-ε = refl
  (x ◅ xs) ◅◅-ε rewrite xs ◅◅-ε = refl
