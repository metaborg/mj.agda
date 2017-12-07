module Categorical.Ofe.Properties where

open import Level
open import Data.Unit using (tt)
open import Data.Nat hiding (_⊔_)
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
_⟨$⟩_ ►⇀ f = ↘ ⟨$⟩ f
cong (►⇀ {A = A}) = ↘-contractive

-- laters can be pushed through exponentials
►⇨ : ∀ {ℓ e e'}{A B : Ofe ℓ e e'} → Ofes [ ► (A ⇨ B) , A ⇨ ► B ]
_⟨$⟩_ (►⇨ {B = B}) f = record
  { _⟨$⟩_ = λ x → f ⟨$⟩ x
  ; cong = λ eq → monotone (► B) (n≤1+n _) (Later.next (cong f eq)) }
cong ►⇨ Later.now _ = Later.now
cong (►⇨ {A = A}) (Later.next feq) xeq = Later.next (feq (monotone A (n≤1+n _) xeq))

module _ {ℓ}{A : Ofe ℓ ℓ ℓ} where
  open import Categories.Object.Terminal (Ofes {ℓ}{ℓ}{ℓ})
  module ⊤ = Terminal terminal
  open import Categories.Morphisms (Ofes {ℓ}{ℓ}{ℓ})

  ⊤⇨A≅A : (⊤.⊤ ⇨ A) ≅ A
  ⊤⇨A≅A = record
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
