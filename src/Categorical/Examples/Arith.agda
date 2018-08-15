module Categorical.Examples.Arith where
{-
  This example demonstrates how the *later* guard and fueled functions
  can be used to build a definitional interpreter for a simple
  arithmetic language.

  This example does not involve intrinsically typed syntax or state.
  It also doesn't necessitate fuel, because we could build the fixpoint in Agda;
  but we do not allow that escape here.
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

-- we specialize here to ofes at universe level zero;
-- all our types and such fit in there
Cat = Ofes {lz}{lz}{lz}

open import Categories.Object.Exponential Cat
open import Categories.Object.Exponentiating Cat binary-products
open import Categories.Object.BinaryProducts Cat
open import Categories.Support.SetoidFunctions as SF using () renaming (→-to-⟶ to lift)

open Category Cat
open BinaryProducts binary-products

private
  data Exp-set : Set where
    num : ℕ → Exp-set
    add : Exp-set → Exp-set → Exp-set

-- our values are just the natural numbers
Val = set→setoid ℕ

-- lift expressions to Ofe trivially
Exp = Δ⁺ Exp-set

module Elim (A : Ofe lz lz lz) where

  Rec = (Exp ⇨ A)

  -- eliminator of the Exp type
  elim : (Rec ×-ofe (Δ⁺ ℕ)) ⇒ A →
         (Rec ×-ofe (Exp ×-ofe Exp)) ⇒ A →
         (Rec ×-ofe Exp) ⇒ A
  _⟨$⟩_ (elim f g) (rec , num n) = f ⟨$⟩ (rec , n)
  _⟨$⟩_ (elim f g) (rec , add e₁ e₂) = g ⟨$⟩ (rec , e₁ , e₂)
  cong (elim f g) {x = rec , num _} (eq , ≣-refl) = cong f (eq , ≣-refl)
  cong (elim f g) {x = rec , add _ _} (eq , ≣-refl) = cong g (eq , ≣-refl , ≣-refl)

-- Make the syntax of manipulating exponentiating available
module _ {X : Obj} where
  open Exponentiating record { exponential = λ {A} → exp A X } public

Eval = Exp ⇨ ⇀ Val

eval-arith : ⊤ ⇒ Eval
eval-arith = μ (Exp ⇨-cofe (⇀-cofe Val)) eval' (⇨-const (⇀-inhabited Val))
  where
    case-num : (Eval × Δ⁺ ℕ) ⇒ ⇀ Val
    case-num = fuel SF.id ∘ π₂ {A = Eval}

    case-add : (Eval × (Exp × Exp)) ⇒ ⇀ Val
    case-add =
        {!!}                                     -- add values
      ∘ _⁂_ {C = Eval × Exp} eval eval          -- recursively evaluate the sub-expressions
      ∘ ×-distrib-× {A = Eval}{B = Exp}{C = Exp} -- fiddling with arguments

    eval' : Ofes [ ► Eval , Eval ]
    eval' =
      λ-abs _ (                                  -- building a function
        Elim.elim (⇀ Val)                        -- eliminate the two expression-cases
            case-num
            case-add
        ∘ first {C = Exp} rec-unfold             -- build the recursor
      )
