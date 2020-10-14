module Data.Nat.Extra where

open import Data.Nat
open import Data.Bool

isZero : ℕ → Bool
isZero 0 = true
isZero (suc _) = false
