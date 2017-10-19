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
open import ScopesFrames.ScopesFrames k Ty

{-
    class Integer {
      int x = 0;
      void set(Integer b) {
        this.x = b.get()
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
  {- set -} mᵗ ((ref (# 1)) ∷ []) void
  ∷ []

Integer : Scope
Integer = # 1

g : Graph
-- root scope
g zero = classes , []
-- class scope of Integer class
g (suc zero)= (intmethods ++ intfields) , zero ∷ []
-- scope of Integer.set method
g (suc (suc zero)) = (vᵗ (ref (# 1)) ∷ []) , # 1 ∷ []
-- scopes of main
g (suc (suc (suc zero))) = vᵗ (ref Integer) ∷ [] , (# 0 ∷ [])
g (suc (suc (suc (suc zero)))) = vᵗ (ref Integer) ∷ [] , # 3 ∷ []
g (suc (suc (suc (suc (suc ())))))

open SyntaxG g
open UsesGraph g

IntegerImpl : Class (# 0) (# 1)
IntegerImpl = class0 {ms = intmethods}{intfields}
  ( -- methods
    (#m' (meth (# 2) (body-void (
      set
        (var (path [] (here refl)))
        (path [] (there (here refl)))
        (get (var (path [] (here refl))) (path [] (there (here refl))))
      ◅ ε
    )))) ∷ [])
  ( -- fields
    (#v' tt) ∷ [])
  []

{-
  int main() {
    Integer x;
    Integer y;
    x = new Integer();
    y = new Integer();
    x.x = 9;
    y.x = 18;
    y.set(x);
    return y.x;
  }
-}
main : Body (# 0) int
main = body
    (
        loc (# 3) (ref Integer)
      ◅ loc (# 4) (ref Integer)
      ◅ asgn (path (here refl ∷ []) (here refl)) (new (path (here refl ∷ here refl ∷ []) (here refl)))
      ◅ asgn (path [] (here refl)) (new (path (here refl ∷ here refl ∷ []) (here refl)))
      ◅ set (var (path (here refl ∷ []) (here refl))) (path [] (there (here refl))) (num (+ 9))
      ◅ set (var (path [] (here refl))) (path [] (there (here refl))) (num (+ 18))
      ◅ run (call (var (path [] (here refl))) (path [] (here refl)) (var (path (here refl ∷ []) (here refl)) ∷ []))
      ◅ ε
    )
    (get (var (path [] (here refl))) (path [] (there (here refl))))

p : Program (# 0) int
p = program classes (#c' (IntegerImpl , # 1 , obj (# 1) ⦃ refl ⦄)  ∷ []) main

open import MJSF.Semantics
open Semantics _ g
open import MJSF.Values
open ValuesG _ g

test : p ⇓⟨ 100 ⟩ (λ v → v ≡ num (+ 18) )
test = refl
