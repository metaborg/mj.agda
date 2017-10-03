module MJSF.Examples.Integer where

open import Prelude
open import Data.Maybe hiding (All)
open import Data.Vec hiding (_∈_; init; _++_)
import Data.Vec.All as Vec∀
open import Data.Star
open import Data.Bool
open import Data.List
open import Data.Integer
open import Data.List.Any
open import Data.List.Any.Membership.Propositional
open import Data.List.All hiding (lookup)
open import Data.Product hiding (Σ)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

k : ℕ
k = 5

open import MJSF.Syntax k
open import ScopeGraph.ScopesFrames k Ty

{-
    class Integer {
      int x = 0;
      int get() {
        return this.x;
      }
      int set(Integer b) {
        this.x = b.get()
        return;
      }
    }
-}

classes : List Ty
classes = (cᵗ (# 0) (# 1) ∷ [])

intmethods intfields : List Ty
intfields =
  {- x -} vᵗ int
  ∷ []
intmethods =
  {- set -} mᵗ ((ref (# 1)) ∷ (ref (# 1)) ∷ []) void
  ∷ []

INT : Scope
INT = # 1

φ : Graph
-- root scope
φ zero = classes , []
-- class scope of INT class
φ (suc zero)= (intmethods ++ intfields) , zero ∷ []
-- scope of INT::set method
φ (suc (suc zero)) = (vᵗ (ref (# 1)) ∷ vᵗ (ref (# 1)) ∷ []) , # 1 ∷ []
-- scopes of main
φ (suc (suc (suc zero))) = vᵗ (ref INT) ∷ [] , (# 0 ∷ [])
φ (suc (suc (suc (suc zero)))) = vᵗ (ref INT) ∷ [] , # 3 ∷ []
φ (suc (suc (suc (suc (suc ())))))

open SyntaxG φ
open UsesGraph φ

IntegerImpl : Class (# 0) (# 1)
IntegerImpl = class0 {ms = intmethods}{intfields}
  ( -- methods
    (#m' (meth (# 2) (body-void (
      set
        (upcast refl (var (path [] (there (here refl)))))
        (path [] (there (here refl)))
        (upcast refl (get (upcast refl (var (path [] (here refl)))) (path [] (there (here refl)))))
      ◅ ε
    )))) ∷ [])
  ( -- fields
    (#v' tt) ∷ [])
  []

-- a simple program
main : Body (# 0) int
main = body
    (
        loc (# 3) (ref INT)
      ◅ loc (# 4) (ref INT)
      ◅ asgn (path (here refl ∷ []) (here refl)) (upcast refl (new (path (here refl ∷ here refl ∷ []) (here refl))))
      ◅ asgn (path [] (here refl)) (upcast refl (new (path (here refl ∷ here refl ∷ []) (here refl))))
      ◅ set (upcast refl (var (path (here refl ∷ []) (here refl)))) (path [] (there (here refl))) (upcast refl (num (+ 9)))
      ◅ set (upcast refl (var (path [] (here refl)))) (path [] (there (here refl))) (upcast refl (num (+ 18)))
      ◅ do (upcast refl (call (upcast refl (var (path [] (here refl)))) (path [] (here refl)) (upcast refl (var (path (here refl ∷ []) (here refl))) ∷ [])))
      ◅ ε
    )
    (upcast refl (get (upcast refl (var (path [] (here refl)))) (path [] (there (here refl)))))

p : Program (# 0) int
p = program classes (#c' IntegerImpl  ∷ []) main

open import MJSF.SemanticsIC
open Semantics _ φ
open import MJSF.Values
open ValuesG _ φ

rootframe : HeapFrame (# 0) (# 0 ∷ [])
rootframe = ((ValuesG.cᵗ IntegerImpl (obj INT ⦃ refl ⦄ ) (here refl)) ∷ []) , []

test : rootframe ⊢ p ⇓⟨ 100 ⟩ (λ v → v ≡ reflv (num (+ 18)) )
test = refl
