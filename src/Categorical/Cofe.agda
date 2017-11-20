open import Categories.Agda
open import Categories.Support.Equivalence using (Setoid)
import Categories.Support.SetoidFunctions as SF

module Categorical.Cofe where

open import Relation.Binary.Core using (Reflexive; Transitive; Symmetric)
open import Relation.Binary using (IsEquivalence)
open import Level using (_⊔_) renaming (suc to lsuc)
open import Data.Nat hiding (_⊔_)
open import Data.Product

open import Categorical.Ofe renaming (_⟶_ to _⟶'_; _⇨_ to _⇨'_)

open Chain

record Cofe s₁ s₂ e : Set (lsuc s₁ ⊔ lsuc s₂ ⊔ lsuc e) where
  field
    ofe : Ofe s₁ s₂ e

  open Ofe ofe public

  field
    -- completeness := every cauchy chain has a limit
    conv : ∀ (c : Chain ofe) → Limit c

open Cofe

module Binary {s₁ s₂ e s₁' s₂' e'}(Left : Cofe s₁ s₂ e)(Right : Cofe s₁' s₂' e') where

  _⟶_ = (Cofe.ofe Left) ⟶' (Cofe.ofe Right)

  .conv-map : {c : Chain (ofe Left)} → (F : _⟶_) →
              (ofe Right) [ at-∞ (conv Right (chain-map F c)) ≋ F ⟨$⟩ (at-∞ (conv Left c)) ]
  conv-map {c} F n =
    begin
      at-∞ (conv Right (chain-map F c))
    ↑⟨ limit (conv Right (chain-map F c)) n ⟩
      (F ⟨$⟩ c at n)
    ↓⟨ cong F (limit (conv Left c) n) ⟩
      (F ⟨$⟩ at-∞ (conv Left c))
    ∎
    where open OfeReasoning (ofe Right)

  _⇨_ : Cofe _ _ _
  _⇨_ = record
    { ofe = Cofe.ofe Left ⇨' Cofe.ofe Right
    ; conv = conv′ }
    where
      chain-apply : ∀ (x : Carrier Left)(c : Chain (ofe Left ⇨' ofe Right)) → Chain (ofe Right)
      chain-apply x c = chain-map (record
        { _⟨$⟩_ = λ f → f ⟨$⟩ x
        ; cong = λ x≈ₙy → x≈ₙy (Ofe.≈ₙ-refl (ofe Left)) }) c

      conv′ : ∀ (c : Chain (ofe Left ⇨' ofe Right)) → Limit c
      -- describe the limit of a function chain
      _⟨$⟩_ (at-∞ (conv′ c)) x =
        at-∞ (Cofe.conv Right (chain-apply x c))
      cong (at-∞ (conv′ c)) {n}{x = x}{y} x≈ₙy =
        begin
          at-∞ (conv Right (chain-apply x c))
        ↑⟨ limit (conv Right (chain-apply x c)) n ⟩
          (c at n) ⟨$⟩ x
        ↓⟨ cong (_at_ c n) x≈ₙy ⟩
          (c at n) ⟨$⟩ y
        ↓⟨ limit (conv Right (chain-apply y c)) n ⟩
          at-∞ (conv Right (chain-apply y c))
        ∎
        where open OfeReasoning (ofe Right)
      -- proof that this is a limit
      limit (conv′ c) n {x = x}{y} x≈ₙy =
        begin
          (c at n) ⟨$⟩ x
        ↓⟨ cong (c at n) x≈ₙy ⟩
          (c at n) ⟨$⟩ y
        ↓⟨ limit (conv Right (chain-apply y c)) n ⟩
          at-∞ (conv Right (chain-apply y c))
        ∎
        where open OfeReasoning (ofe Right)

open Binary
open import Categories.Category

Cofes : ∀ {c ℓ e} → Category _ _ _
Cofes {c}{ℓ}{e} = record {
  Obj = Cofe c ℓ e;
  _⇒_ = _⟶_ ;
  _≡_ = λ {o}{o'} f g → Cofe._≈_ (o ⇨ o')  f g ;
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
conv (Δ s) c = lim (c at zero) (λ n → cauchy c z≤n z≤n)
