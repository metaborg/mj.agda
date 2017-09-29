module MJ.Examples.Exceptions where

open import Prelude
open import Data.Star
open import Data.Maybe hiding (All)
open import Data.Vec hiding (_∈_; init)
import Data.Vec.All as Vec∀
open import Data.List
open import Data.List.Any
open import Data.List.Any.Membership.Propositional
open import Data.List.All hiding (lookup)
open import Data.Product hiding (Σ)
open import Relation.Binary.PropositionalEquality

open import MJ.Examples.Integer

open import MJ.Types
open import MJ.Classtable
open import MJ.Classtable.Code Σ
open import MJ.Syntax Σ
open import MJ.Syntax.Program Σ
open import MJ.Semantics Σ Lib
open import MJ.Semantics.Values Σ

-- Integer class body

caught : Prog int
caught = Lib , let
    x = (here refl)
    y = (there (here refl))
    v = (there (there (here refl)))
  in body
    (
      loc int
      ◅ loc (ref INT)
      ◅ loc (ref INT)
      ◅ asgn v (num 0)
      ◅ asgn x (new INT (num 9 ∷ []))
      ◅ asgn y (new INT (num 18 ∷ []))
      ◅ (try (block (
          -- perform a side effect on the heap: writing 18 to x's int field
          do (call (var x) "set" {_}{void} (var y ∷ []))
          -- raise the exception
          ◅ raise
          ◅ ε
        )) catch (block (
          -- read the 18 from x's field
          asgn v (call (var x) "get" [])
          ◅ ε
        )))
      ◅ ε
    )
    (var v)

uncaught : Prog int
uncaught = Lib , let
    x = (here refl)
    y = (there (here refl))
    v = (there (there (here refl)))
  in body
    (
      loc int
      ◅ loc (ref INT)
      ◅ loc (ref INT)
      ◅ asgn v (num 0)
      ◅ asgn x (new INT (num 9 ∷ []))
      ◅ asgn y (new INT (num 18 ∷ []))
      ◅ asgn v (call (var x) "get" [])
      ◅ raise
      ◅ ε
    )
    (var v)

test : caught ⇓⟨ 100 ⟩ (λ v → v ≡ num 18)
test = refl

test₂ : uncaught ⇓⟨ 100 ⟩! (λ μ e → e ≡ other)
test₂ = refl
