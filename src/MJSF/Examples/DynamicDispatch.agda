module MJSF.Examples.DynamicDispatch where

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
k = 10

open import MJSF.Syntax k
open import ScopeGraph.ScopesFrames k Ty

{-
  class Int {

      public int x;

      public int get() {
          System.out.println("never");
          return x;
      }

      public int inc(Int y) {
          x = y.x;
          return this.get();
      }
  }

  class IntInc extends Int {

      public int get() {
          return x + 1;
      }

      public int doinc(Int y) {
          Int x = new Int();
          x.x = y.x + 1;
          return inc(x);
      }
  }

  class Main {
      public static void main(String[] args) {
          Int y = new Int();
          y.x = 18;
          IntInc x = new IntInc();
          x.x = 0;

          // should print 20 because we use the get() of IntInc
          System.out.println(x.doinc(y));
      }
  }
-}

Root : Scope
Root = # 0

Int : Scope
Int = # 1

IntInc : Scope
IntInc = # 2

-- Main class omitted; main() function is given below, as child scope
-- of the root scope.

classes : List Ty
classes = (cᵗ Root Int ∷
           cᵗ Root IntInc ∷ [])

Int-methods Int-fields : List Ty
Int-fields =
  {- x -} vᵗ int
  ∷ []
Int-methods =
  {- Int.get -} mᵗ [] int ∷
  {- Int.inc -} mᵗ (ref Int ∷ []) int ∷
  []

IntInc-methods IntInc-fields : List Ty
IntInc-methods =
  -- {- IntInc.get -} mᵗ [] int ∷
  {- IntInc.doinc -} mᵗ (ref Int ∷ []) int ∷
  []
IntInc-fields = []

g : Graph
-- root scope
g zero =
  classes , []

-- class scope of Int class
g (suc zero) =
  (Int-methods ++ Int-fields) , zero ∷ []
-- class scope of IntInc class
g (suc (suc zero)) =
  (IntInc-methods ++ IntInc-fields) , zero ∷ # 1 ∷ []

-- scope of Int.get method; 3
g (suc (suc (suc zero))) =
  [] , Int ∷ []
-- scope of Int.inc method; 4
g (suc (suc (suc (suc zero)))) =
  vᵗ (ref Int) ∷ [] , Int ∷ []

-- scope of IntInc.get method; 5
g (suc (suc (suc (suc (suc zero))))) =
  [] , IntInc ∷ []
-- scope of IntInc.doinc method; 6
g (suc (suc (suc (suc (suc (suc zero)))))) =
  vᵗ (ref Int) ∷ [] , IntInc ∷ []

-- local variable scope of Int.doinc method; 7
g (suc (suc (suc (suc (suc (suc (suc zero))))))) =
  vᵗ (ref Int) ∷ [] , # 6 ∷ []

-- x local variable scope of Main.main method; 8
g (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) =
  vᵗ (ref Int) ∷ [] , Root ∷ []

-- y local variable scope of Main.main method; 9
g (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) =
  vᵗ (ref IntInc) ∷ [] , # 8 ∷ []

g (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc ()))))))))))

open SyntaxG g
open UsesGraph g

IntImpl : Class Root Int
IntImpl =
  class0 {ms = Int-methods} {fs = Int-fields}
    -- methods
    (#m' (meth (# 3)
               (body ε
                     (var (path ((here refl) ∷ []) (there (there (here refl))))))) ∷
    (#m' (meth (# 4)
               (body (asgn (path ((here refl) ∷ []) (there (there (here refl))))
                           (get (var (path [] (here refl))) (path [] (there (there (here refl))))) ◅
                           ε)
                     (call (this [] (here refl))
                           (path [] (here refl))
                           [])))) ∷ [])
    -- fields
    ((#v' tt) ∷ [])
    -- overrides
    []

IntIncImpl : Class Root IntInc
IntIncImpl =
  class1 {ms = IntInc-methods} {fs = IntInc-fields}
    -- path to parent
    (path [] (here refl))
    -- methods
    (#m' (meth (# 6)
               (body ((loc (# 7) (ref Int)) ◅
                      asgn (path [] (here refl))
                           (new (path ((here refl) ∷ ((here refl) ∷ ((here refl) ∷ [])))
                                      (here refl))) ◅
                      (set (var (path [] (here refl)))
                           (path [] (there (there (here refl))))
                           (iop Data.Integer._+_
                                (get (var (path ((here refl) ∷ []) (here refl)))
                                     (path [] (there (there (here refl)))))
                                (num (+ 1)))) ◅
                      ε)
               (call (this (here refl ∷ []) (here refl))
                     (path (there (here refl) ∷ []) (there (here refl)))
                     ((var (path [] (here refl))) ∷ [])))) ∷
    [])
    -- fields
    []
    -- overrides
    (((path ((there (here refl)) ∷ []) (here refl)) ,
    (meth (# 5)
           (body ε
                 (iop Data.Integer._+_
                      (var (path ((here refl) ∷ ((there (here refl)) ∷ []))
                                 (there (there (here refl)))))
                      (num (+ 1)))))) ∷ [])

main : Body Root int
main =
  body ((loc (# 8) (ref Int)) ◅
       ((asgn (path [] (here refl))
              (new (path (here refl ∷ [])
                   (here refl)))) ◅
       (set (var (path [] (here refl)))
            (path [] (there (there (here refl))))
            (num (+ 18))) ◅
       (loc (# 9) (ref IntInc)) ◅
       ((asgn (path [] (here refl))
              (new (path (here refl ∷ here refl ∷ [])
                         (there (here refl))))) ◅
       ((set (var (path [] (here refl)))
             (path (there (here refl) ∷ []) (there (there (here refl))))
             (num (+ 0))) ◅
       ε))))
       (call (var (path [] (here refl)))
             (path [] (here refl))
             ((var (path ((here refl) ∷ []) (here refl))) ∷ []))


p : Program Root int
p = program classes
            (#c' (IntImpl , Int , obj Int ⦃ refl ⦄) ∷
            (#c' (IntIncImpl , Int , (super ⦃ refl ⦄ (obj Int ⦃ refl ⦄)))) ∷
            []) main

open import MJSF.Semantics
open Semantics _ g
open import MJSF.Values
open ValuesG _ g

test : p ⇓⟨ 100 ⟩ (λ v → v ≡ num (+ 20) )
test = refl
