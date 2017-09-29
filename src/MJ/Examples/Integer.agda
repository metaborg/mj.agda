module MJ.Examples.Integer where

open import Prelude
open import Data.Maybe hiding (All)
open import Data.Vec hiding (_∈_; init)
import Data.Vec.All as Vec∀
open import Data.Star
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

open import MJ.Classtable.Core 1

INT : Cid 1
INT = (cls (# 0))

decls : (ns : NS) → List (String × typing ns)
decls METHOD =
    ("get" , ([] , int))
  ∷ ("set" , (ref INT ∷ [] , void))
  ∷ []
decls FIELD =
    ("x" , int)
  ∷ []

IntegerSig = (class Object (int ∷ []) decls)

-- class table signature
Σ : Classtable
Σ = record {
  Σ = λ{
    (cls zero) → IntegerSig ;
    (cls (suc ())) ;
    Object → ObjectClass} ;
  founded = refl ;
  rooted = λ{
    (cls zero) → super ◅ ε ;
    (cls (suc ())) ;
    Object → ε };
  Σ-Object = refl }

open import MJ.Classtable.Code Σ
open import MJ.Syntax Σ
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
          unit))

      ∷ []
    )

-- Implementation of the class table
Lib : Code
Lib (cls zero) = IntegerImpl
Lib (cls (suc ()))
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
        loc (ref INT)
      ◅ loc (ref INT)
      ◅ asgn x (new INT ((num 9) ∷ []))
      ◅ asgn y (new INT ((num 18) ∷ []))
      ◅ do (call (var x) "set" {_}{void} (var y ∷ []))
      ◅ ε
    )
    (get (var x) "x")

test0 : p₀ ⇓⟨ 100 ⟩ (λ {W} (v : Val W int) → v ≡ num 18)
test0 = refl
