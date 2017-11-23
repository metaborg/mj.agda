open import Categories.Agda
open import Categories.Support.Equivalence using (Setoid)
import Categories.Support.SetoidFunctions as SF

module Categorical.Ofe.Cofe where

open import Relation.Binary.Core using (Reflexive; Transitive; Symmetric)
open import Relation.Binary using (IsEquivalence)
open import Level using (_⊔_) renaming (suc to lsuc)
open import Data.Nat hiding (_⊔_)
open import Data.Product

open import Categorical.Ofe renaming (_⇨_ to _⇨'_)

open Chain

record Cofe o e e' : Set (lsuc o ⊔ lsuc e ⊔ lsuc e') where
  field
    ofe : Ofe o e e'

  open Ofe ofe public

  field
    -- completeness := every cauchy chain has a limit
    conv : ∀ (c : Chain ofe) → Limit c

open Cofe

module Binary {s₁ s₂ e s₁' s₂' e'}(Left : Ofe s₁ s₂ e)(Right : Cofe s₁' s₂' e') where

  _⇨_ : Cofe _ _ _
  _⇨_ = record
    { ofe = Left ⇨' Cofe.ofe Right
    ; conv = conv′ }
    where
      chain-apply : ∀ (x : Ofe.Carrier Left)(c : Chain (Left ⇨' ofe Right)) → Chain (ofe Right)
      chain-apply x c = chain-map (record
        { _⟨$⟩_ = λ f → f ⟨$⟩ x
        ; cong = λ x≈ₙy → x≈ₙy (Ofe.≈ₙ-refl Left) }) c

      conv′ : ∀ (c : Chain (Left ⇨' ofe Right)) → Limit c
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

open Binary using (_⇨_) public
open import Categories.Category

-- lifting Setoids to degenerate Cofes
Δ : ∀ {o e} → Setoid o e → Cofe o e e
ofe  (Δ s) = record
  { setoid = s
  ; _≈⟨_⟩_ = λ x _ y → Setoid._≈_ s x y
  ; equiv = Setoid.isEquivalence s
  ; limit₁ = λ eq _ → eq
  ; limit₂ = λ eq → eq zero
  ; monotone = λ _ eq → eq }
conv (Δ s) c = lim (c at zero) (λ n → cauchy c z≤n z≤n)

.conv-map : ∀ {o e e'}{A B : Cofe o e e'}{c : Chain (ofe A)} → (F : (ofe A) ⟶ (ofe B)) →
            (ofe B) [ at-∞ (conv B (chain-map F c)) ≋ F ⟨$⟩ (at-∞ (conv A c)) ]
conv-map {A = A}{B}{c} F n =
  begin
    at-∞ (conv B (chain-map F c))
  ↑⟨ limit (conv B (chain-map F c)) n ⟩
    (F ⟨$⟩ c at n)
  ↓⟨ cong F (limit (conv A c) n) ⟩
    (F ⟨$⟩ at-∞ (conv A c))
  ∎
  where open OfeReasoning (ofe B)

-- limits preserve approximate equality
.cong-conv : ∀ {s₁ s₂ e}(A : Cofe s₁ s₂ e) → (l r : Chain (Cofe.ofe A)) → ∀ {n} →
             l chain≈⟨ n ⟩ r → (Cofe.ofe A) [ at-∞ (Cofe.conv A l) ≈⟨ n ⟩ at-∞ (Cofe.conv A r) ]
cong-conv A l r {n} eq =
  begin
    at-∞ (Cofe.conv A l)
  ↑⟨ limit (Cofe.conv A l) n ⟩
    l at n
  ↓⟨ eq n ⟩
    r at n
  ↓⟨ limit (Cofe.conv A r) n ⟩
    at-∞ (Cofe.conv A r)
  ∎
  where open OfeReasoning (Cofe.ofe A)
