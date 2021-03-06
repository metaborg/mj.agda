module MJ.Examples.While where

open import MJ.Examples.Integer

open import Prelude
open import MJ.Types
open import MJ.Classtable.Code Σ
open import MJ.Syntax Σ
open import MJ.Syntax.Program Σ
open import MJ.Semantics Σ Lib
open import MJ.Semantics.Values Σ
open import Data.List.Any
open import Data.List.Membership.Propositional
open import Data.Star
open import Data.Bool as Bools hiding (_≤?_)
open import Relation.Nullary.Decidable

-- a simple program that computes 10 using a while loop
p₁ : Prog int
p₁ = Lib ,
  let
    x = (here refl)
  in body
    (
        loc int
      ◅ asgn x (num 1)
      ◅ while iop (λ x y → Bools.if ⌊ suc x ≤? y ⌋ then 0 else 1) (var x) (num 10) run (
        asgn x (iop (λ x y → x + y) (var x) (num 1))
      )
      -- test simplest if-then-else and early return from statement
      ◅ if (num 0) then (ret (var x)) else (ret (num 0))
      ◅ ε
    )
    (num 0)

test1 : p₁ ⇓⟨ 100 ⟩ (λ {W} (v : Val W int) → v ≡ num 10)
test1 = refl
