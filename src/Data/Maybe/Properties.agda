module Data.Maybe.Properties where

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Maybe

just-not-nothing : ∀ {ℓ}{A : Set ℓ}{x : Maybe A}{y : A} → x ≡ just y → ¬ (x ≡ nothing)
just-not-nothing refl = λ ()
