module MJ.Examples.While where

open import MJ.Examples.Integer

open import Prelude
open import MJ.Types
open import MJ.Classtable.Code Σ
open import MJ.Syntax Σ
open import MJ.Syntax.Program Σ
open import MJ.Semantics Σ Lib hiding (_>>=_; return)
open import MJ.Semantics.Values Σ
open import Data.Maybe
open import Data.List.Any
open import Data.List.Any.Membership.Propositional
open import Data.Star hiding (_>>=_; return)
open import Data.Bool as Bools
open import Relation.Nullary.Decidable

-- a simple program that computes 10 using a while loop
count : ℕ → Prog int
count n = Lib ,
  let
    x = (here refl)
  in body
    (
        loc int
      ◅ asgn x (num 1)
      ◅ while iop (λ x y → Bools.if ⌊ suc x ≤? y ⌋ then 0 else 1) (var x) (num n) run (
        asgn x (iop (λ x y → x + y) (var x) (num 1))
      )
      -- test simplest if-then-else and early return from statement
      ◅ if (num 0) then (ret (var x)) else (ret (num 0))
      ◅ ε
    )
    (num 0)

import IO.Primitive as Prim
open import IO as IO
open import Data.String
open import Coinduction

main : Prim.IO ⊤
main = IO.run (do
  (just v) ← (♯ return (returns-val (eval 999999999 (count 10000)))) -- return (returns-val (eval 100 p₁))
    where nothing → ♯ putStr "Err"
  ♯ putStr (show-val (proj₂ v)))

test1 : (count 10) ⇓⟨ 1000 ⟩ (λ {W} (v : Val W int) → v ≡ num 10)
test1 = refl
