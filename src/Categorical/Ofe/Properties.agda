module Categorical.Ofe.Properties where

open import Level
open import Data.Unit using (tt)
open import Data.Nat hiding (_⊔_; _+_)
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality as PEq using () renaming (refl to ≣-refl; _≡_ to _≣_)

open import Categories.Support.Equivalence
open import Categories.Category

open import Categorical.Ofe
open import Categorical.Ofe.Exponentials
open import Categorical.Ofe.Products
open import Categorical.Ofe.Later
open import Categorical.Ofe.StepIndexed

open _⟶_
open Ofe

-- laters disappear on fueled functions
►⇀ : ∀ {e e'}{A : Setoid e e'} → Ofes [ ► (⇀ A) , (⇀ A) ]
_⟨$⟩_ ►⇀ (next f) = ↘ ⟨$⟩ f
cong (►⇀ {A = A}) {x = next f}{y = next g} = ↘-contractive

-- laters can be pushed through exponentials
-- TODO minimal primitive; this one should follow;
-- TODO Applicative?
►⇨ : ∀ {ℓ e e'}{A B : Ofe ℓ e e'} → Ofes [ ► (A ⇨ B) , A ⇨ ► B ]
_⟨$⟩_ (►⇨ {B = B}) (next f) = record
  { _⟨$⟩_ = λ x → next (f ⟨$⟩ x)
  ; cong = λ eq → monotone (► B) (n≤1+n _) (Later.next (cong f eq)) }
cong ►⇨ Later.now _ = Later.now
cong (►⇨ {A = A}) (Later.next feq) xeq = Later.next (feq (monotone A (n≤1+n _) xeq))

module _ {ℓ} where
  -- the following properties hold only when
  -- when the objects and equalities of the Ofes live in the same universe
  private
    Cat = Ofes {ℓ}{ℓ}{ℓ}

  open Category Cat
  open import Categories.Object.Terminal Cat
  open import Categories.Object.Exponential Cat
  open import Categories.Object.BinaryProducts Cat
  open import Categories.Morphisms Cat

  module ⊤ = Terminal terminal

  ⊤⇨A≅A : ∀ {A : Ofe ℓ ℓ ℓ} → (⊤.⊤ ⇨ A) ≅ A
  ⊤⇨A≅A {A} = record
    { f = from
    ; g = to
    ; iso = record
      { isoˡ = λ f≈g _ → f≈g (lift tt)
      ; isoʳ = λ eq    → eq }}
    where
      from : Ofes [ ⊤.⊤ ⇨ A , A ]
      _⟨$⟩_ from f = f ⟨$⟩ lift tt
      cong from feq = feq (lift tt)

      to : Ofes [ A , ⊤.⊤ ⇨ A  ]
      _⟨$⟩_ to a = record { _⟨$⟩_ = λ _ → a ; cong = λ _ → ≈ₙ-refl A }
      cong to aeq = λ _ → aeq

  rec-unfold : ∀ {A : Ofe ℓ ℓ ℓ}{B : Setoid ℓ ℓ} → Ofes [ ► (A ⇨ ⇀ B) , (A ⇨ ⇀ B) ]
  rec-unfold {A}{B} =
    [ exp A (⇀ B) ]λ Binary.product (
        ►⇀
      ∘ [ exp _ _ ]eval
      ∘ Binary.first {C = A} ►⇨
    )

module _ {o e e'}{A B C : Ofe o e e'} where
  private
    Cat = Ofes {o}{e}{e'}

  open Category Cat

  open import Categorical.Ofe.Coproducts as Cop

  open import Categories.Object.BinaryProducts Cat
  open import Categories.Object.Coproduct Cat

  open BinaryProducts binary-products
  open BinCoproducts Cop.binary renaming ([_,_] to case[_,_])

  ×-distrib-+ : (A × (B + C)) ⇒ (A × B) + (A × C)
  _⟨$⟩_ ×-distrib-+ x with π₂ {A = A}{B = B + C} ⟨$⟩ x
  ... | inj₁ y = inj₁ (π₁ {A = A}{B = B + C} ⟨$⟩ x , y)
  ... | inj₂ y = inj₂ (π₁ {A = A}{B = B + C} ⟨$⟩ x , y)
  cong ×-distrib-+ (eq₁ , inj₁ eq₂) = inj₁ (eq₁ , eq₂)
  cong ×-distrib-+ (eq₁ , inj₂ eq₂) = inj₂ (eq₁ , eq₂)

  ×-distrib-× : (A × (B × C)) ⇒ ((A × B) × (A × C))
  _⟨$⟩_ ×-distrib-× (l , m , r) = (l , m) , (l , r)
  cong ×-distrib-× (e , e' , e'') = (e , e') , (e , e'')
