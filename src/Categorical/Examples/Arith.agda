module Categorical.Examples.Arith where

open import Level using () renaming (zero to lz)
open import Data.Nat as Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using () renaming (refl to ≣-refl)

open import Categories.Category
open import Categories.Support.Equivalence

open import Categorical.Ofe
open import Categorical.Ofe.Cofe renaming (_⇨_ to _⇨-cofe_)
open import Categorical.Ofe.Products
open import Categorical.Ofe.Coproducts as Cop
open import Categorical.Ofe.Exponentials
open import Categorical.Ofe.Later
open import Categorical.Ofe.StepIndexed
open import Categorical.Ofe.Properties

Ofes₀ = Ofes {lz}{lz}{lz}

open import Categories.Object.Coproduct Ofes₀
open import Categories.Object.Exponential Ofes₀
open import Categories.Object.Exponentiating Ofes₀ binary-products
open import Categories.Object.BinaryProducts Ofes₀
open import Categories.Support.SetoidFunctions as SF using () renaming (→-to-⟶ to lift)

open Category Ofes₀
open BinaryProducts binary-products
open BinCoproducts Cop.binary renaming ([_,_] to case[_,_])

module _ {A B C : Obj} where
  ×-distrib-+ : (A × (B + C)) ⇒ (A × B) + (A × C)
  _⟨$⟩_ ×-distrib-+ x with π₂ {A = A}{B = B + C} ⟨$⟩ x
  ... | inj₁ y = inj₁ (π₁ {A = A}{B = B + C} ⟨$⟩ x , y)
  ... | inj₂ y = inj₂ (π₁ {A = A}{B = B + C} ⟨$⟩ x , y)
  cong ×-distrib-+ (eq₁ , inj₁ eq₂) = inj₁ (eq₁ , eq₂)
  cong ×-distrib-+ (eq₁ , inj₂ eq₂) = inj₂ (eq₁ , eq₂)

  ×-distrib-× : (A × (B × C)) ⇒ ((A × B) × (A × C))
  _⟨$⟩_ ×-distrib-× (l , m , r) = (l , m) , (l , r)
  cong ×-distrib-× (e , e' , e'') = (e , e') , (e , e'')

private
  data Exp-set : Set where
    num : ℕ → Exp-set
    add : Exp-set → Exp-set → Exp-set

Val = set→setoid ℕ
Exp = Δ⁺ Exp-set

destruct : Exp ⇒ (Δ⁺ ℕ) + (Exp ×-ofe Exp)
destruct = record
  { _⟨$⟩_ = λ where
     (num n) → inj₁ n
     (add l r) → inj₂ (l , r)
  ; cong = λ where
     {x = num _  } ≣-refl → inj₁ ≣-refl
     {x = add _ _} ≣-refl → inj₂ (≣-refl , ≣-refl) }

eval-arith : ⊤ ⇒ (Exp ⇨ ⇀ Val)
eval-arith = μ (Exp ⇨-cofe (⇀-cofe Val)) eval' (⇨-const (⇀-inhabited Val))
  where
    module _ {X : Obj} where
      open Exponentiating record { exponential = λ {A} → exp A X } public
    module _ {A B : Obj} where
      open Exponential (exp A B) public hiding (eval)

    Rec = ► (Exp ⇨ ⇀ Val)

    -- a helper to call the recursor with one fuel less
    rec : (Rec × Exp) ⇒ ⇀ Val
    rec =
        eval
      ∘ first {A = Rec}{B = (Exp ⇨ ⇀ Val)}{C = Exp} (
            λ-abs _ (►⇀ ∘ eval)
          ∘ ►⇨
        )

    case-num : (Rec × Δ⁺ ℕ) ⇒ ⇀ Val
    case-num = fuel SF.id ∘ π₂ {A = Rec}

    case-add : (Rec × (Exp × Exp)) ⇒ ⇀ Val
    case-add =
        {!!}                                        -- add values
      ∘ _⁂_ {A = Rec × Exp}{C = Rec × Exp} rec rec -- recursively evaluate the sub-expressions
      ∘ ×-distrib-× {A = Rec}{B = Exp}{C = Exp}     -- fiddling with arguments

    eval' : Ofes [ Rec , (Exp ⇨ ⇀ Val) ]
    eval' =
      λ-abs _ (
          case[ case-num , case-add ] -- case-tree for handling the two cases of expressions
        ∘ ×-distrib-+ {A = Rec}       -- fiddling with arguments
        ∘ second {A = Rec} destruct   -- destruct the input expression
      )
