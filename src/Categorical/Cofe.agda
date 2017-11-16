open import Categories.Agda
open import Categories.Support.Equivalence using (Setoid)
import Categories.Support.SetoidFunctions as SF

module Categorical.Cofe where

open import Relation.Binary.Core using (Reflexive; Transitive; Symmetric)
open import Relation.Binary using (IsEquivalence)
open import Level using (_⊔_) renaming (suc to lsuc)
open import Data.Nat hiding (_⊔_)
open import Data.Product

open import Categorical.Ofe renaming (_⟶_ to _⟶'_)

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
_⟶_ o o' = (Cofe.ofe o) ⟶' (Cofe.ofe o')

open import Categories.Category

Cofes : ∀ {c ℓ e} → Category _ _ _
Cofes {c}{ℓ}{e} = record {
  Obj = Cofe c ℓ e;
  _⇒_ = _⟶_ ;
  _≡_ = λ {o}{o'} f g → Ofe._≈_ (ofe o ⇨ ofe o')  f g ;
  id  = Category.id Ofes ;
  _∘_ = Category._∘_ Ofes;
  assoc = λ {_ _ _ _}{f g h} x≈y → assoc {f = f}{g}{h} x≈y ;
  identityʳ = λ {_ _}{f} → identityʳ {f = f};
  identityˡ = λ {_ _}{f} → identityˡ {f = f} ;
  equiv = λ {A B} → Category.equiv Ofes ;
  ∘-resp-≡ = λ {_ _ _}{f h g i} → ∘-resp-≡ {f = f}{h}{g}{i} }
  where open Category Ofes

-- lifting Setoids to degenerate Cofes
Δ : ∀ {s₁ s₂} → Setoid s₁ s₂ → Cofe _ _ _
ofe  (Δ s) = record
               { setoid = s
               ; _≈⟨_⟩_ = λ x _ y → Setoid._≈_ s x y
               ; equiv = Setoid.isEquivalence s
               ; limit₁ = λ eq _ → eq
               ; limit₂ = λ eq → eq zero
               ; monotone = λ _ eq → eq
               }
conv (Δ s) = λ c → c at zero , λ n → cauchy c z≤n z≤n

► : ∀ {s₁ s₂ e} → Cofe s₁ s₂ e → Cofe _ _ _
► T = record
  { ofe = {!!}
  ; conv = {!!} }
