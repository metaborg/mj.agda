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

module Elim (A : Ofe lz lz lz) where

  Rec = (Exp ⇨ A)

  elim : (Rec ×-ofe (Δ⁺ ℕ)) ⇒ A →
             (Rec ×-ofe (Exp ×-ofe Exp)) ⇒ A →
             (Rec ×-ofe Exp) ⇒ A
  _⟨$⟩_ (elim f g) (rec , num n) = f ⟨$⟩ (rec , n)
  _⟨$⟩_ (elim f g) (rec , add e₁ e₂) = g ⟨$⟩ (rec , e₁ , e₂)
  cong (elim f g) {x = rec , num _} (eq , ≣-refl) = cong f (eq , ≣-refl)
  cong (elim f g) {x = rec , add _ _} (eq , ≣-refl) = cong g (eq , ≣-refl , ≣-refl)

module Eval where

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
          {!E!}                                    -- add values
        ∘ _⁂_ {C = Eval × Exp} eval eval          -- recursively evaluate the sub-expressions
        ∘ ×-distrib-× {A = Eval}{B = Exp}{C = Exp} -- fiddling with arguments

      eval' : Ofes [ ► Eval , (Exp ⇨ ⇀ Val) ]
      eval' =
        λ-abs _ (
            Elim.elim (⇀ Val) case-num case-add
          ∘ first {C = Exp} rec-unfold
        )
