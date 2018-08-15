module MJ.Examples.DynDispatch where

open import Prelude
open import Data.Maybe hiding (All)
open import Data.Vec hiding (_∈_; init)
import Data.Vec.All as Vec∀
open import Data.Star
open import Data.Integer hiding (suc)
open import Data.Bool
open import Data.List
open import Data.List.Any
open import Data.List.Any.Membership.Propositional
open import Data.List.All hiding (lookup)
open import Data.Product hiding (Σ)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Data.String

open import MJ.Types

open import MJ.Classtable.Core 2

{-

  // We test field inheritance and
  // method call dispatching combining super calls and dynamic dispatch.
  // The Agda test is equivalent to the following Java code

  class Int {

      int x;

      public Int(int i) {
          this.x = i;
          return;
      }

      public int get() {
          System.out.println("never");
          return x;
      }

      public int set (Int y) {
          x = y.x;

          // in the test main this should dispatch to
          // the implementation of the child Int2
          return this.get();
      }
  }

  class Int2 extends Int {

      public Int2(int i) {
          super(i);
      }

      public int get() {
          return x + 1;
      }

      public int set (Int y) {
          // test super dispatch
          return super.set(new Int(y.x + 1));
      }
  }

  class Main {
      public static void main(String[] args) {
          Int y = new Int(18);
          Int2 x = new Int2(0);

          // should print 20
          // because we use the set(..) and get() of Int2
          // which both increment with one
          System.out.println(x.set(y));
      }
  }

-}

INT : Cid 2
INT = (cls (# 0))

INT+ : Cid 2
INT+ = (cls (# 1))

decls : (ns : NS) → List (String × typing ns)
decls METHOD =
    ("get" , ([] , int))
  ∷ ("set" , (ref INT ∷ [] , int))
  ∷ []
decls FIELD =
    ("x" , int)
  ∷ []

-- override methods; no extra fields
decls+ : (ns : NS) → List (String × typing ns)
decls+ METHOD =
    ("get" , ([] , int))
  ∷ ("set" , (ref INT ∷ [] , int))
  ∷ []
decls+ FIELD = []

IntegerSig = (class Object (int ∷ []) decls)
Integer+Sig = (class INT (int ∷ []) decls+)

-- class table signature
Σ : Classtable
Σ = record {
  Σ = λ{
    (cls zero) → IntegerSig ;
    (cls (suc zero)) → Integer+Sig ;
    (cls (suc (suc ()))) ;
    Object → ObjectClass} ;
  founded = refl ;
  rooted = λ{
    (cls zero) → super ◅ ε ;
    (cls (suc zero)) → super ◅ super ◅ ε ;
    (cls (suc (suc ()))) ;
    Object → ε };
  Σ-Object = refl }

open import MJ.Classtable.Code Σ
open import MJ.Syntax Σ
import MJ.Syntax.BinOp as BOp
open import MJ.Syntax.Program Σ

-- Integer class body
IntegerImpl : Implementation INT
IntegerImpl = implementation
    (body (body
      (set
        (var (here refl))
        "x"
        (var (there (here refl))) ◅ ε)
      unit))

    -- methods
    (
      -- get
      body (body ε (get (var (here refl)) "x"))

      -- set
      ∷ (body (body
          (set
            (var (here refl))
            "x"
            {int}
            (get (var (there (here refl))) "x") ◅ ε)
          (call (var (here refl)) "get" [])))

      ∷ []
    )

-- Integer+ class body
Integer+Impl : Implementation INT+
Integer+Impl = implementation
    (body (body
      (
        set (var (here refl)) "x" (var (there (here refl)))
        ◅ ε)
      unit))

    -- methods
    (
      -- override get
      (body (body ε (bop BOp.+ (get (var (here refl)) "x") (num (+ 1)))))

      -- set
      ∷ (super _ ⟨ new INT (bop BOp.+ (get (var (there (here refl))) "x") (num (+ 1)) ∷ []) ∷ [] ⟩then
        body
          ε
          (var (here refl)))

      ∷ []
    )

-- Implementation of the class table
Lib : Code
Lib (cls zero) = IntegerImpl
Lib (cls (suc zero)) = Integer+Impl
Lib (cls (suc (suc ())))
Lib Object = implementation (body (body ε unit)) []

open import MJ.Semantics Σ Lib
open import MJ.Semantics.Values Σ

-- a simple program
p₀ : Prog int
p₀ = Lib ,
  let
    x = (here refl)
    y = (there (here refl))
  in body
    (
        loc (ref INT) -- y
      ◅ loc (ref INT+) -- x
      ◅ asgn x (new INT+ ((num (+ 0)) ∷ []))
      ◅ asgn y (new INT ((num (+ 18)) ∷ []))
      ◅ ε
    )
    (call (var x) "set" (var y ∷ []))

test0 : p₀ ⇓⟨ 100 ⟩ (λ {W} (v : Val W int) → v ≡ num (+ 20))
test0 = refl
