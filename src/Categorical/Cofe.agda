open import Categories.Agda
open import Categories.Support.Equivalence using (Setoid)
import Categories.Support.SetoidFunctions as SF

module Categorical.Cofe where

open import Relation.Binary.Core using (Reflexive; Transitive; Symmetric)
open import Relation.Binary using (IsEquivalence)
open import Level using (_⊔_) renaming (suc to lsuc)
open import Data.Nat hiding (_⊔_)
open import Data.Product

open import Categorical.Ofe using (Ofes; Limit; Ofe; Chain; chain-map) renaming (_⇨_ to _⇨'_; _⟶_ to _⟶'_)

open Chain

record Cofe s₁ s₂ e : Set (lsuc s₁ ⊔ lsuc s₂ ⊔ lsuc e) where
  field
    ofe : Ofe s₁ s₂ e

  open Ofe ofe public

  field
    -- completeness := every cauchy chain has a limit
    .conv : ∀ (c : Chain ofe) → Limit c

open Cofe public

_⟶_ : ∀ {s₁ s₂ e s₁' s₂' e'} → Cofe s₁ s₂ e → Cofe s₁' s₂' e' → Set _
_⟶_ o o' = (ofe o) ⟶' (ofe o')

open import Categories.Category

Cofes : ∀ {c ℓ e} → Category _ _ _
Cofes {c}{ℓ}{e} = record {
  Obj = Cofe c ℓ e;
  _⇒_ = _⟶_ ;
  _≡_ = λ {o}{o'} f g → Ofe._≈_ (ofe o ⇨' ofe o')  f g ;
  id  = id ;
  _∘_ = _∘_;
  assoc = λ {_ _ _ _}{f g h} x≈y → assoc {f = f}{g}{h} x≈y ;
  identityʳ = λ {_ _}{f} → identityʳ {f = f};
  identityˡ = λ {_ _}{f} → identityˡ {f = f} ;
  equiv = λ {A B} → Category.equiv Ofes ;
  ∘-resp-≡ = λ {_ _ _}{f h g i} → ∘-resp-≡ {f = f}{h}{g}{i} }
  where open Category Ofes
