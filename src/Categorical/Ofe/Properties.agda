module Categorical.Ofe.Properties where

open import Data.Nat
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
cong (►⇀ {A = A}) {x = x}{y} Later.now z≤n =
  trans (x ⟨0⟩) (sym (y ⟨0⟩))
  where open Setoid (MaybeS A)
cong (►⇀ {A = A}) {x = x}{y} (Later.next x≈y) m≤n =
  x≈y (∸-mono {u = 1}{v = 1} m≤n (≤-reflexive ≣-refl))

-- laters can be pushed through exponentials
►⇨ : ∀ {ℓ e e'}{A B : Ofe ℓ e e'} → Ofes [ ► (A ⇨ B) , A ⇨ ► B ]
_⟨$⟩_ (►⇨ {B = B}) f = record
  { _⟨$⟩_ = λ x → f ⟨$⟩ x
  ; cong = λ eq → monotone (► B) (n≤1+n _) (Later.next (cong f eq)) }
cong ►⇨ Later.now _ = Later.now
cong (►⇨ {A = A}) (Later.next feq) xeq = Later.next (feq (monotone A (n≤1+n _) xeq))
