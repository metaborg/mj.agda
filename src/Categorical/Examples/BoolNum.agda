{-# OPTIONS --show-implicit #-}
module Categorical.Examples.BoolNum where
{-
  This example builds on Categorical.Examples.Arith

  We add a type bool and the corresponding value and expressions.
  To ensure soundness-by-construction we type the expression and value syntax.

  The interpreter structure remains the same, but the expression-elimination
  is more involved.
-}

open import Level using () renaming (zero to lz)
open import Data.Nat as Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using () renaming (refl to ≣-refl)

open import Categories.Category
open import Categories.Support.Equivalence

open import Categorical.Ofe
open import Categorical.Ofe.Cofe renaming (_⇨_ to _⇨-cofe_)
open import Categorical.Ofe.Products
open import Categorical.Ofe.Exponentials
open import Categorical.Ofe.Later
open import Categorical.Ofe.StepIndexed
open import Categorical.Ofe.Properties
open import Categorical.Ofe.Predicates
open import Categorical.Ofe.Predicates.Properties
open import Categorical.Ofe.Predicates.Closures

-- we specialize here to ofes at universe level zero;
-- all our types and such fit in there
Cat = Ofes {lz}{lz}{lz}

open import Categories.Object.Exponential Cat
open import Categories.Object.Exponentiating Cat binary-products
open import Categories.Object.BinaryProducts Cat
open import Categories.Support.SetoidFunctions as SF using () renaming (→-to-⟶ to lift)

open Category Cat
open BinaryProducts binary-products

data Type : Set where
  bool : Type
  int  : Type

data Exp-set : Type → Set where
  num : ℕ → Exp-set int
  add : Exp-set int → Exp-set int → Exp-set int

data Val-set : Type → Set where
  num        : ℕ → Val-set int
  true false : Val-set bool

-- our values are just the natural numbers
Val : Type → Setoid lz lz
Val a = set→setoid (Val-set a)

-- lift expressions to Ofe trivially
Exp : Type → Obj
Exp a = Δ⁺ (Exp-set a)

module Elim (A : Type → Obj) where

  Rec = ∀[ Type ] λ a → (Exp a ⇨ A a)

  -- eliminator of the Exp type
  elim : (Rec ×-ofe (Δ⁺ ℕ)) ⇒ A int →
         (Rec ×-ofe (Exp int ×-ofe Exp int)) ⇒ A int →
         ∀ {a} → (Rec ×-ofe (Exp a)) ⇒ A a
  _⟨$⟩_ (elim f g) (rec , num n) = f ⟨$⟩ (rec , n)
  _⟨$⟩_ (elim f g) (rec , add e₁ e₂) = g ⟨$⟩ (rec , e₁ , e₂)
  cong (elim f g) {x = rec , num _} (eq , ≣-refl) = cong f (eq , ≣-refl)
  cong (elim f g) {x = rec , add _ _} (eq , ≣-refl) = cong g (eq , ≣-refl , ≣-refl)

-- Make the syntax of manipulating exponentiating available
module _ {X : Obj} where
  open Exponentiating record { exponential = λ {A} → exp A X } public

Eval = ∀[ Type ] λ a → Exp a ⇨ ⇀ (Val a)

eval-arith : ⊤ ⇒ Eval
eval-arith =
  μ
    (∀[ Type ]-cofe λ a → (Exp a ⇨-cofe (⇀-cofe Val a)))  -- the type of the interpreter is cauchy-complete
    eval-arith'                                           -- interpreter with guarded recursor
    (λ a → ⇨-const (⇀-inhabited (Val a)))                 -- initial element
  where

    -- generalizes the evaluation of an exponent
    -- to the polymorphic exponent matching Eval.
    eval' : ∀ {a} → Ofes [ Eval ×-ofe Exp a , ⇀ (Val a) ]
    eval' {a} = eval ∘ first {C = Exp a} (∀-elim {A = λ a → (Exp a ⇨ (⇀ Val a))} a)

    case-num : (Eval × Δ⁺ ℕ) ⇒ ⇀ (Val int)
    case-num = fuel (lift num) ∘ π₂ {A = Eval}

    case-add : (Eval × (Exp int × Exp int)) ⇒ ⇀ (Val int)
    case-add =
        {!!}                                             -- add values
      ∘ _⁂_ {C = Eval × Exp int} eval' eval'            -- recursively evaluate the sub-expressions
      ∘ ×-distrib-× {A = Eval}{B = Exp int}{C = Exp int} -- fiddling with arguments

    eval-arith' : ► Eval ⇒ Eval
    eval-arith' =
      ∀-intro (λ a →
        λ-abs {Γ = ► Eval} (Exp a) (
            Elim.elim (λ a → ⇀ Val a) case-num case-add
          ∘ first {A = ► Eval}{B = Eval}{C = Exp a} (
              ∀-intro (λ a → rec-unfold ∘ ∀-elim a)
            ∘ ►∀
          )
        )
      )
