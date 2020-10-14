
module Data.Nat.Properties.Extra where

open import Data.Nat.Base
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Empty

≤′-unique : ∀ {i u} (p q : i ≤′ u) → p ≡ q
≤′-unique ≤′-refl ≤′-refl = refl
≤′-unique ≤′-refl (≤′-step q) = ⊥-elim (1+n≰n (≤′⇒≤ q))
≤′-unique (≤′-step p) ≤′-refl = ⊥-elim (1+n≰n (≤′⇒≤ p))
≤′-unique (≤′-step p) (≤′-step q) = cong ≤′-step (≤′-unique p q)

m+n+o≡n+m+o : ∀ m n o → m + (n + o) ≡ n + (m + o)
m+n+o≡n+m+o m n o = begin
  m + (n + o) ≡⟨ sym (+-assoc m n o) ⟩
  (m + n) + o ≡⟨ cong (λ x → x + o) (+-comm m n) ⟩
  (n + m) + o ≡⟨ +-assoc n m o ⟩
  n + (m + o) ∎
