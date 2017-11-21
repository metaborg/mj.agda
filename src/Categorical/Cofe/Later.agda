module Categorical.Cofe.Later where

open import Relation.Binary.PropositionalEquality using () renaming (refl to ≣-refl)
open import Categories.Support.Equivalence using (Setoid)
open import Categories.Support.EqReasoning
open import Relation.Binary using (IsEquivalence)
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Unit hiding (setoid; _≤_)
open import Level

open import Categorical.Ofe renaming (_⇨_ to _⇨'_)
open import Categorical.Ofe.Later renaming (► to Ofe►)
open import Categorical.Cofe

► : ∀ {s₁ s₂ e} → Cofe s₁ s₂ e → Cofe _ _ _
► T = record
  { ofe = Ofe► (Cofe.ofe T)
  ; conv = conv' }
  where
    open Cofe T
    open Later ofe

    unfold-chain : ∀ (c : Chain (Ofe► ofe)) → Chain ofe
    _at_   (unfold-chain c) n = (c at (ℕ.suc n))
    cauchy (unfold-chain c) {i = i}{j} n≤i n≤j = unnextₙ (cauchy c (s≤s n≤i) (s≤s n≤j))

    conv' : (c : Chain (Ofe► ofe)) → Limit c
    at-∞  (conv' c) = at-∞ (Cofe.conv T (unfold-chain c))
    limit (conv' c) n =
      begin
        c at n
      ↓⟨ cauchy c (≤-reflexive ≣-refl) (n≤1+n n) ⟩
        c at ℕ.suc n
      ↓⟨ Ofe.monotone (Ofe► ofe) (n≤1+n n) (next (limit (conv (unfold-chain c)) n)) ⟩
        at-∞ (conv (unfold-chain c))
      ∎
      where open OfeReasoning (Ofe► ofe)

open import Categories.Category
open Cofe

-- we can build a fixed point from a contractive function
μ' : ∀ {s₁ s₂ e}{A : Cofe s₁ s₂ e} →
     (F : Ofes [ ofe A , ofe A ]) → .(Contractive F) → Ofes [ ofe A , ofe A ]
_⟨$⟩_ (μ' {A = A} F p) x = at-∞ (Cofe.conv A (iterate F p x))
cong  (μ' {A = A} F p) {n = n}{x = x}{y} x≈y =
  cong-conv A
    (iterate F p x)
    (iterate F p y)
    (iterate-cong F F p p (NE.≈-cong _ _ F) x≈y)

-- Because we can build contractive functions from non-expansive functions from ◀ A to A,
-- we can define a μ that is slightly easier to work with.
μ : ∀ {s₁ s₂ e}{A : Cofe s₁ s₂ e} → (F : Cofes [ ► A , A ]) → Cofes [ A , A ]
μ {A = A} F = μ' {A = A} (Ofes [ F ∘ next-ne (Cofe.ofe A) ]) ([ F ∘ next-ne (Cofe.ofe A) ]-contractive next-co)
