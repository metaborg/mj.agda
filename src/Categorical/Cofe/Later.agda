module Categorical.Cofe.Later where

open import Relation.Binary.PropositionalEquality using () renaming (refl to ≣-refl)
open import Categories.Support.Equivalence using (Setoid)
open import Relation.Binary using (IsEquivalence)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Unit hiding (setoid; _≤_)
open import Level

open import Categorical.Ofe
open import Categorical.Ofe.Later using (module Later) renaming (► to Ofe►)
open import Categorical.Cofe

► : ∀ {s₁ s₂ e} → Cofe s₁ s₂ e → Cofe _ _ _
► {s₁}{s₂}{e} T = record
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
