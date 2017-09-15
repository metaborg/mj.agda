open import Relation.Binary hiding (_⇒_)

module Experiments.Category {ℓ₁ ℓ₂ ℓ₃} (APO : Preorder ℓ₁ ℓ₂ ℓ₃) where

open import Level
open Preorder APO
open import Function as Fun using (flip)
open import Relation.Unary using (Pred)
import Relation.Binary.PropositionalEquality as PropEq
open PropEq.≡-Reasoning

record IsMP {ℓ}(P : Carrier → Set ℓ) : Set (ℓ ⊔ ℓ₁ ⊔ ℓ₃) where
  field
    monotone : ∀ {c c'} → c ∼ c' → P c → P c'

-- monotone predicates over a fixed carrier
record MP ℓ : Set (suc ℓ ⊔ ℓ₁ ⊔ ℓ₃) where
  constructor mp
  field
    pred  : Pred Carrier ℓ
    is-mp : IsMP pred

  open IsMP is-mp public

-- application
_·_ : ∀ {ℓ} → MP ℓ → Carrier → Set _
(mp P _) · c = P c

-- product
open import Data.Product
infixl 30 _⊗_
_⊗_ : ∀ {ℓ₁ ℓ₂} → MP ℓ₁ → MP ℓ₂ → MP (ℓ₁ ⊔ ℓ₂)
P ⊗ Q = mp
    (λ c → (P · c) × (Q · c))
    (record {
      monotone = λ{ c~c' (p , q) →
          MP.monotone P c~c' p
        , MP.monotone Q c~c' q
      }
    })

_⇒_ : ∀ {ℓ₁ ℓ₂} → MP ℓ₁ → MP ℓ₂ → Set _
P ⇒ Q = ∀ {c} → P · c → Q · c

-- monotone-predicate equality
_≗_ : ∀ {ℓ₁} → MP ℓ₁ → MP ℓ₁ → Set _
P ≗ Q = ∀ {c} → P · c PropEq.≡ Q · c

_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃}{P : MP ℓ₁}{Q : MP ℓ₂}{R : MP ℓ₃} → P ⇒ Q → Q ⇒ R → P ⇒ R
F ∘ G = λ p → G (F p)

id : ∀ {ℓ}(P : MP ℓ) → P ⇒ P
id P = Fun.id

MP₀ = MP zero

-- the underlying ~ relations is itself a monotone predicate
~mp : ∀ c → IsMP (_∼_ c)
~mp c = record { monotone = flip trans }

-- it's easy to lift predicates to monotone predicates
pack : ∀ {ℓ} → Pred Carrier ℓ → MP _
pack P = mp
  (λ c → ∃ λ c' → c' ∼ c × P c') (record {
    monotone = λ{ c~c' (c'' , c~c'' , pc') → c'' , trans c~c'' c~c' , pc' }
  })

module Properties where
  -- associativity
  ∘-assoc : ∀ {ℓ₁}{P Q R S : MP ℓ₁}{F : P ⇒ Q}{G : Q ⇒ R}{H : R ⇒ S} →
            ∀ {c}(p : P · c) →
            (_∘_ {P = P}{Q}{S} F (_∘_ {P = Q}{R}{S} G H)) p
            PropEq.≡
            (_∘_ {P = P}{R}{S} (_∘_ {P = P}{Q}{R} F G) H) p
  ∘-assoc p = PropEq.refl

  ∘-left-id : ∀ {P Q : MP ℓ₁}{F : P ⇒ Q} →
              ∀ {c}(p : P · c) → (_∘_ {P = P}{P}{Q} (id P) F) p PropEq.≡ F p
  ∘-left-id {P = P}{Q}{F} p = PropEq.refl

  ∘-right-id : ∀ {P Q : MP ℓ₁}{F : P ⇒ Q} →
              ∀ {c}(p : P · c) → (_∘_ {P = P}{Q}{Q} F (id Q)) p PropEq.≡ F p
  ∘-right-id {P = P}{Q}{F} p = PropEq.refl
