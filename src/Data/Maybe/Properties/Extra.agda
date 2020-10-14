module Data.Maybe.Properties.Extra {a}{A : Set a} where

open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

nothing≢just : ∀ {a : A} → ¬ (_≡_ {A = Maybe A} nothing (just a))
nothing≢just ()
