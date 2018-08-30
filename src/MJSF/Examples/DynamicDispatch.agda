module MJSF.Examples.DynamicDispatch where

open import Prelude
open import Data.Maybe hiding (All)
open import Data.Vec hiding (init; _++_)
import Data.Vec.All as Vec∀
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

k = 10

open import MJSF.Syntax
open import ScopesFrames.ScopeGraph Ty ℕ Bool

{-
  class Int {

      public int x;

      public int get() {
          System.out.println("never");
          return x;
      }

      public int set(Int y) {
          x = y.x;
          return this.get();
      }
  }

  class IntInc extends Int {

      public int get() {
          return x + 1;
      }

      public int inc(Int y) {
          Int x = new Int();
          x.x = y.x + 1;
          return set(x);
      }
  }

  class Main {
      public static void main(String[] args) {
          Int y = new Int();
          y.x = 18;
          IntInc x = new IntInc();
          x.x = 0;

          // should print 20 because we use the get() of IntInc
          System.out.println(x.inc(y));
      }
  }
-}

Root : Scope k
Root = # 0

Int : Scope k
Int = # 1

IntInc : Scope k
IntInc = # 2

-- Main class omitted; main() function is given below, as child scope
-- of the root scope.

classes : Decls k
classes = ((0 , cᵗ Root Int) ∷
           (1 , cᵗ Root IntInc) ∷ [])

Int-methods Int-fields : Decls k
Int-fields =
  {- x -} (2 , vᵗ int)
  ∷ []
Int-methods =
  {- Int.get -} (3 , mᵗ [] int) ∷
  {- Int.set -} (4 , mᵗ (ref Int ∷ []) int) ∷
  []

IntInc-methods IntInc-fields : Decls k
IntInc-methods =
  -- {- IntInc.get -} mᵗ [] int ∷
  {- IntInc.inc -} (5 , mᵗ (ref Int ∷ []) int) ∷
  []
IntInc-fields = []

g : Graph
g = mkGraph k
      ( (classes , []) -- root scope
      ∷ ((Int-methods ++ Int-fields) , (true , # 0) ∷ []) -- class scope of Int class
      ∷ ((IntInc-methods ++ IntInc-fields) , (true , # 0) ∷ (false , # 1) ∷ []) -- class scope of IntInc class
      ∷ ([] , (true , Int) ∷ []) -- scope of Int.get method; 3
      ∷ ((6 , vᵗ (ref Int)) ∷ [] , (true , Int) ∷ []) -- scope of Int.set method; 4
      ∷ ([] , (true , IntInc) ∷ []) -- scope of IntInc.get method; 5
      ∷ ((6 , vᵗ (ref Int)) ∷ [] , (true , IntInc) ∷ []) -- scope of IntInc.inc method; 6
      ∷ ((7 , vᵗ (ref Int)) ∷ [] , (true , # 6) ∷ []) -- local variable scope of Int.inc method; 7
      ∷ ((7 , vᵗ (ref Int)) ∷ [] , (true , Root) ∷ []) -- x local variable scope of Main.main method; 8
      ∷ ((6 , vᵗ (ref IntInc)) ∷ [] , (true , # 8) ∷ []) -- y local variable scope of Main.main method; 9
      ∷ [])

open Syntax {g}

IntImpl : Class Root Int
IntImpl =
  class0 {ms = Data.List.map proj₂ Int-methods} {fs = Data.List.map proj₂ Int-fields}
    -- methods
    (#m' (meth (# 3)
               (body ε
                     (var (path⇣ ((here refl) ∷ []) (there (there (here refl))))))) ∷
    (#m' (meth (# 4)
               (body ( asgn (path⇣ ((here refl) ∷ [])
                                  (there (there (here refl))))
                            (get (var (path⇣ [] (here refl)))
                                 (path⇣ [] (there (there (here refl)))))
                     ◅ ε)
                     (call (this [] (here refl))
                           (path⇣ [] (here refl))
                           [])))) ∷ [])
    -- fields
    ((#v' tt) ∷ [])
    -- overrides
    []

IntIncImpl : Class Root IntInc
IntIncImpl =
  class1 {ms = Data.List.map proj₂ IntInc-methods} {fs = Data.List.map proj₂ IntInc-fields}
    -- path to parent
    (path⇣ [] (here refl))
    -- methods
    (#m'
      (meth
        (# 6)
        (body
        ( loc (# 7) (ref Int)
        ◅ asgn (path⇣ [] (here refl))
               (new (path⇣ ((here refl) ∷ ((here refl) ∷ ((here refl) ∷ [])))
                             (here refl)))
        ◅ set (var (path⇣ [] (here refl)))
                  (path⇣ [] (there (there (here refl))))
                  (iop Data.Integer._+_
                       (get (var (path⇣ ((here refl) ∷ []) (here refl)))
                            (path⇣ [] (there (there (here refl)))))
                       (num (+ 1)))
        ◅ ε)
      (call (this (here refl ∷ []) (here refl))
            (path⇣ (there (here refl) ∷ []) (there (here refl)))
            ((var (path⇣ [] (here refl))) ∷ [])))) ∷
    [])
    -- fields
    []
    -- overrides
    (#m'
     (path⇣ ((there (here refl)) ∷ []) (here refl) ,
     (meth
       (# 5)
       (body
         ε
         (iop Data.Integer._+_
              (var (path⇣ ((here refl) ∷ ((there (here refl)) ∷ []))
                         (there (there (here refl)))))
                   (num (+ 1)))))) ∷ [])

main : Body Root int
main =
  body
    ( (loc (# 8) (ref Int))
    ◅ asgn (path⇣ [] (here refl))
           (new (path⇣ (here refl ∷ []) (here refl)))
    ◅ set (var (path⇣ [] (here refl)))
          (path⇣ [] (there (there (here refl))))
          (num (+ 18))
    ◅ loc (# 9) (ref IntInc)
    ◅ asgn (path⇣ [] (here refl))
           (new (path⇣ (here refl ∷ here refl ∷ [])
                      (there (here refl))))
    ◅ set (var (path⇣ [] (here refl)))
          (path⇣ (there (here refl) ∷ []) (there (there (here refl))))
          (num (+ 0))
    ◅ ε)

    (call (var (path⇣ [] (here refl)))
          (path⇣ [] (here refl))
          (var (path⇣ ((here refl) ∷ []) (here refl)) ∷ []))


p : Program Root int
p = program (Data.List.map proj₂ classes)
            (#c' (IntImpl , Int , obj Int ⦃ refl ⦄) ∷
            (#c' (IntIncImpl , Int , (super ⦃ refl ⦄ (obj Int ⦃ refl ⦄)))) ∷
            []) main

open import MJSF.Semantics
open Semantics g
open import MJSF.Values
open Values {g}

test : p ⇓⟨ 100 ⟩ (λ v → v ≡ num (+ 20) )
test = refl
