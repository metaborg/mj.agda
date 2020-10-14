module Data.List.First.Properties {ℓ}{A : Set ℓ} where

open import Data.Product
open import Data.List
open import Data.List.Any
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Empty
open import Data.List.First
open import Data.List.Membership.Propositional

first⟶∈ : ∀ {B : A → Set} {x l} → First B x l → (x ∈ l × B x)
first⟶∈ (here {x = x} p) = here refl , p
first⟶∈ (there x' ¬px f) with (first⟶∈ f)
first⟶∈ (there x' ¬px f) | x∈l , p = there x∈l , p

first-unique : ∀ {P : A → Set}{x y v} → First P x v → First P y v → x ≡ y
first-unique (here x) (here y) = refl
first-unique (here {x = x} px) (there .x ¬px r) = ⊥-elim (¬px px)
first-unique (there x ¬px l) (here {x = .x} px) = ⊥-elim (¬px px)
first-unique (there x' _ l) (there .x' _ r) = first-unique l r
