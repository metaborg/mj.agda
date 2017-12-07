module Categorical.Ofe.StepIndexed where

open import Level
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as PEq using () renaming (refl to ≣-refl; _≡_ to _≣_)
open import Relation.Binary.Core using (IsEquivalence)
open import Function.Equivalence as Eqv using (_⇔_; Equivalence; equivalence)
import Function

open import Categories.Category
open import Categories.Functor.Core

open import Categorical.Ofe hiding (_[_≈_])
open import Categorical.Ofe.Cofe
open import Categorical.Thin

open import Categorical.Ofe.Predicates
open import Categories.Support.Equivalence
open import Categorical.ISetoids.Equality
open import Data.Maybe hiding (setoid)

open Thin ℕ≤
open Category
open Functor
open Setoid

-- We are using the Category library's definition of setoids (with an irrelevant equivalence)
MaybeS : ∀ {s₁ s₂} → Setoid s₁ s₂ → Setoid _ _
Carrier (MaybeS A) = Maybe (Carrier A)
_≈_ (MaybeS A) = Eq (_≈_ A)
isEquivalence (MaybeS A) = Eq-isEquivalence (isEquivalence A)

module StepIndexed {ℓ ℓ'}(A : Setoid ℓ ℓ') where
  -- fueled monotone functions with strong bi-similarity

  record ⇀_ : Set (ℓ ⊔ ℓ') where
    infixl 100 _⟨_⟩
    field
      _⟨_⟩ : ℕ → Maybe (Carrier A)
      _⟨0⟩ : MaybeS A [ _⟨_⟩ 0 ≈ nothing ]
      monotone : ∀ {m n x} → m ≤ n →
                 (MaybeS A) [ _⟨_⟩ m ≈ just x ] → (MaybeS A) [ _⟨_⟩ n ≈ just x ]

  open ⇀_ public

  ⇀-setoid : Setoid _ _
  Carrier ⇀-setoid = ⇀_
  _≈_ ⇀-setoid a b = ∀ n → (MaybeS A) [ a ⟨ n ⟩ ≈ b ⟨ n ⟩ ]
  isEquivalence ⇀-setoid = record
    { refl = λ n → MA.refl
    ; sym = λ p n → MA.sym (p n)
    ; trans = λ p q n → MA.trans (p n) (q n) }
    where module MA = Setoid (MaybeS A)

  open Ofe
  ⇀-ofe : Ofe _ _ _
  setoid ⇀-ofe = ⇀-setoid
  _≈⟨_⟩_ ⇀-ofe f n g = ∀ {m} → m ≤ n → (MaybeS A) [ f ⟨ m ⟩ ≈ g ⟨ m ⟩ ]
  equiv ⇀-ofe = record
    { refl = λ m≤n → MA.refl
    ; sym = λ p m≤n → MA.sym (p m≤n)
    ; trans = λ p q m≤n → MA.trans (p m≤n) (q m≤n) }
    where module MA = Setoid (MaybeS A)
  limit₁ ⇀-ofe = λ p n m≤n → p _
  limit₂ ⇀-ofe = λ p n → p n (≤-reflexive ≣-refl)
  monotone ⇀-ofe {x = f}{g} n≥n' eqₙ m≤n = eqₙ (≤-trans m≤n n≥n')

  inhabited : ⇀_
  _⟨_⟩ inhabited x = nothing
  _⟨0⟩ inhabited = nothing
  monotone inhabited _ ()

open StepIndexed using (_⟨_⟩; monotone; _⟨0⟩) renaming (⇀-ofe to ⇀_) public

-- subtract 1 fuel
↘ : ∀ {e e'}{A : Setoid e e'} → Ofes [ ⇀ A ,  ⇀ A ]
_⟨$⟩_ ↘ f = record
  { _⟨_⟩ = λ n → f ⟨ n ∸ 1 ⟩
  ; _⟨0⟩ = f ⟨0⟩
  ; monotone = λ {m n} m≤n eq → monotone f (∸-mono {u = 1}{v = 1} m≤n (≤-reflexive ≣-refl)) eq }
  where open Data.Nat.Properties
cong ↘ x≈y {m} m≤n = x≈y (≤-trans (n∸m≤n 1 m) m≤n)
