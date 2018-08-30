module MJSF.Examples.Integer where

open import Prelude
open import Data.Maybe hiding (All)
open import Data.Vec hiding (init; _++_)
import Data.Vec.All as Vec∀
open import Data.Unit
open import Data.Star
open import Data.Bool
open import Data.List
open import Data.Integer
open import Data.List.Any
open import Data.List.Membership.Propositional
open import Data.List.All hiding (lookup)
open import Data.Product hiding (Σ)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable


k = 5

open import MJSF.Syntax
open import ScopesFrames.ScopeGraph Ty ℕ Bool

{-
    class Integer {
      int x = 0;
      void set(Integer b) {
        this.x = b.get()
      }
    }
-}

classes : Decls k
classes = ((0 , cᵗ (# 0) (# 1)) ∷ [])

intmethods intfields : Decls k
intfields =
  {- x -} (1 , vᵗ int)
  ∷ []
intmethods =
  {- set -} (2 , mᵗ ((ref (# 1)) ∷ []) void)
  ∷ []

Integer : Scope k
Integer = # 1

g : Graph
g =
  mkGraph 5
    ( (classes , []) -- root scope
    ∷ ((intmethods ++ intfields) , (true , # 0) ∷ []) -- class scope of Integer class
    ∷ (((3 , vᵗ (ref (# 1))) ∷ []) , ((true , # 1) ∷ [])) -- scope of Integer.set method
    ∷ ((4 , vᵗ (ref Integer)) ∷ [] , ((true , # 0) ∷ [])) -- scope of main (1)
    ∷ ((5 , vᵗ (ref Integer)) ∷ [] , (true , # 3) ∷ []) -- scope of main (2)
    ∷ [])

open Syntax {g}

IntegerImpl : Class (# 0) (# 1)
IntegerImpl = class0 {ms = Data.List.map proj₂ intmethods}{Data.List.map proj₂ intfields}{[]}
  (-- methods
    (#m' (meth (# 2) (body-void
    (set
      (this [] (here refl))
      (path⇣ [] (there (here refl)))
      (get (var (path⇣ [] (here refl))) (path⇣ [] (there (here refl))))
    ◅ ε)))) ∷ [])
  (-- fields
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
      ◅ asgn (path⇣ (here refl ∷ []) (here refl)) (new (path⇣ (here refl ∷ here refl ∷ []) (here refl)))
      ◅ asgn (path⇣ [] (here refl)) (new (path⇣ (here refl ∷ here refl ∷ []) (here refl)))
      ◅ set (var (path⇣ (here refl ∷ []) (here refl))) (path⇣ [] (there (here refl))) (num (+ 9))
      ◅ set (var (path⇣ [] (here refl))) (path⇣ [] (there (here refl))) (num (+ 18))
      ◅ run (call (var (path⇣ [] (here refl))) (path⇣ [] (here refl)) (var (path⇣ (here refl ∷ []) (here refl)) ∷ []))
      ◅ ε
    )
    (get (var (path⇣ [] (here refl))) (path⇣ [] (there (here refl))))

p : Program (# 0) int
p = program (Data.List.map proj₂ classes) (#c' (IntegerImpl , # 1 , obj (# 1) ⦃ refl ⦄)  ∷ []) main

open import MJSF.Semantics
open Semantics g
open import MJSF.Values
open Values {g}

test : p ⇓⟨ 100 ⟩ (λ v → v ≡ num (+ 9) )
test = refl
