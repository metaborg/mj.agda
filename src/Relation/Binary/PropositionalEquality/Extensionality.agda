import Relation.Binary.PropositionalEquality as PEq

module Relation.Binary.PropositionalEquality.Extensionality
  (funext : ∀ {ℓ₁ ℓ₂} → PEq.Extensionality ℓ₁ ℓ₂) where


funext² : ∀ {p q r}{P : Set p}{Q : P → Set q}
          {R : (p : P) → Q p → Set r} →
          {f g : ∀ (p : P)(q : Q p) → R p q} → (∀ p q → f p q PEq.≡ g p q) →
          f PEq.≡ g
funext² f = funext λ p → funext λ q → f p q

funext³ : ∀ {p q r s}{P : Set p}{Q : P → Set q}
          {R : (p : P) → Q p → Set r}{S : (p : P)(q : Q p) → R p q → Set s} →
          {f g : ∀ (p : P)(q : Q p)(r : R p q) → S p q r} → (∀ p q r → f p q r PEq.≡ g p q r) →
          f PEq.≡ g
funext³ f = funext λ p → funext λ q → funext λ r → f p q r
