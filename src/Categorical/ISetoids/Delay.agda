open import Categories.Support.Equivalence

module Categorical.ISetoids.Delay {s₁ s₂}(A : Setoid s₁ s₂) where

open import Categories.Functor
open import Categories.Bifunctor
open import Categories.Agda
open import Categories.Category
open import Categories.Support.SetoidFunctions
open import Categories.Object.Product

open import Data.Product
open import Function as Fun
open import Size
open import Level

open Functor
open _⟶_
open Setoid A

mutual
  data Delay (i : Size) : Set s₁ where
    now   : Carrier → Delay i
    later : ∞Delay i → Delay i

  record ∞Delay (i : Size) : Set s₁ where
    coinductive
    field
      force : {j : Size< i} → Delay j

open ∞Delay public
open import Function

-- strong bisimilarity
mutual
  data _≅_ {i : Size} : (?a ?b : Delay ∞) → Set s₂ where
    now   : ∀ {a b : Carrier} → a ≈ b → now a ≅ now b
    later : ∀ {∞a ∞b}(eq : ∞a ∞≅⟨ i ⟩ ∞b) → later ∞a ≅ later ∞b

  _≅⟨_⟩_ : Delay ∞ → Size → Delay ∞ → Set s₂
  _≅⟨_⟩_ = λ a? i b? → _≅_ {i = i} a? b?

  record _∞≅⟨_⟩_ (∞a : ∞Delay ∞) i (∞b : ∞Delay ∞) : Set s₂ where
    coinductive
    field
      .≅force : {j : Size< i} → (force ∞a) ≅⟨ j ⟩ force ∞b

open _∞≅⟨_⟩_ public

_∞≅_ : ∀ {i : Size}(∞a : ∞Delay ∞) (∞b : ∞Delay ∞) → Set s₂
_∞≅_ {i} a∞ b∞ = a∞ ∞≅⟨ i ⟩ b∞

mutual
  .refl' : ∀ {a∞ : Delay ∞} → a∞ ≅ a∞
  refl' {a∞ = now x} = now refl
  refl' {a∞ = later x} = later ∞refl'

  .∞refl' : ∀ {i} {a∞ : ∞Delay ∞} → a∞ ∞≅⟨ i ⟩ a∞
  ≅force (∞refl' {a∞ = a∞}) = refl'

mutual
  .sym' : ∀ {i} {a∞ b∞ : Delay ∞} → a∞ ≅⟨ i ⟩ b∞ → b∞ ≅⟨ i ⟩ a∞
  sym' (now eq) = now (sym eq)
  sym' (later eq) = later (∞sym' eq)

  .∞sym' : ∀ {i} {a∞ b∞ : ∞Delay ∞} → a∞ ∞≅⟨ i ⟩ b∞ → b∞ ∞≅⟨ i ⟩ a∞
  ≅force (∞sym' z) = sym' (≅force z)

mutual
  .trans' : ∀ {i} {a∞ b∞ c∞ : Delay ∞} → a∞ ≅⟨ i ⟩ b∞ → b∞ ≅⟨ i ⟩ c∞ → a∞ ≅⟨ i ⟩ c∞
  trans' (now a) (now b) = now (trans a b)
  trans' (later eq) (later eq₁) = later (∞trans eq eq₁)

  .∞trans : ∀ {i}{a∞ b∞ c∞ : ∞Delay ∞} → a∞ ∞≅⟨ i ⟩ b∞ → b∞ ∞≅⟨ i ⟩ c∞ → a∞ ∞≅⟨ i ⟩ c∞
  ≅force (∞trans p q) = trans' (≅force p) (≅force q)

open Setoid using (Carrier; _≈_; isEquivalence)

delay-setoid : Setoid _ _
Carrier delay-setoid = Delay ∞
_≈_ delay-setoid = _≅_
isEquivalence delay-setoid = record
  { refl = refl'
  ; sym = sym'
  ; trans = trans' }

∞delay-setoid : Setoid _ _
Carrier ∞delay-setoid = ∞Delay ∞
_≈_ ∞delay-setoid = _∞≅_
isEquivalence ∞delay-setoid = record
  { refl = ∞refl'
  ; sym = ∞sym'
  ; trans = ∞trans }
