module MJ.Examples.While where

open import MJ.Examples.Integer

open import Prelude
open import MJ.Types
open import MJ.Syntax Σ
open import MJ.Semantics Σ Lib
open import MJ.Semantics.Values Σ
open import Data.List.Any
open import Data.List.Any.Membership.Propositional
open import Data.Star
open import Data.Bool
open import Relation.Nullary.Decidable

-- a simple program that computes 10
p₁ : Prog int
p₁ = Lib ,
  let
    x = (here refl)
  in body
    (
        loc int
      ◅ asgn x (num 1)
      ◅ while iop (λ x y → if ⌊ suc x ≤? y ⌋ then 0 else 1) (var x) (num 10) do (
        asgn x (iop (λ x y → x + y) (var x) (num 1))
      ) ◅ ε
    )
    (var x)

test1 : p₁ ⇓ (λ {W} (v : Val W int) → v ≡ num 10)
test1 = refl
