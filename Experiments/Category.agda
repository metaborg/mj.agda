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

MP₀ = MP zero

-- application
_·_ : ∀ {ℓ} → MP ℓ → Carrier → Set _
(mp P _) · c = P c

-- monotone-predicate equality
_≗_ : ∀ {ℓ₁} → MP ℓ₁ → MP ℓ₁ → Set _
P ≗ Q = ∀ {c} → P · c PropEq.≡ Q · c

-- we package the Agda function that represents morphisms
-- in this category in a record such that P ⇒ Q doesn't get
-- reduced to the simple underlying type of `apply`
record _⇒_ {p q}(P : MP p)(Q : MP q) : Set (p ⊔ q ⊔ ℓ₁) where
  constructor mk⇒
  field
    apply : ∀ {c} → P · c → Q · c

open _⇒_

infixl 100 _∘_
_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃}{P : MP ℓ₁}{Q : MP ℓ₂}{R : MP ℓ₃} → P ⇒ Q → Q ⇒ R → P ⇒ R
F ∘ G = mk⇒ λ p → apply G (apply F p)

id : ∀ {ℓ}(P : MP ℓ) → P ⇒ P
id P = mk⇒ Fun.id

-- morphism equality
infixl 20 _⇒≡_
_⇒≡_  : ∀ {ℓ₁ ℓ₂}{P : MP ℓ₁}{Q : MP ℓ₂}(F G : P ⇒ Q) → Set _
_⇒≡_ {P = P}{Q} F G = ∀ {c}(p : P · c) → apply F p PropEq.≡ apply G p

module Properties where
  ∘-assoc : ∀ {p q r s}{P : MP p}{Q : MP q}{R : MP r}{S : MP s}
              {F : P ⇒ Q}{G : Q ⇒ R}{H : R ⇒ S} →
              F ∘ (G ∘ H) ⇒≡ (F ∘ G) ∘ H
  ∘-assoc _ = PropEq.refl

  ∘-left-id : ∀ {P Q : MP ℓ₁}{F : P ⇒ Q} → (id P) ∘ F ⇒≡ F
  ∘-left-id _ = PropEq.refl

  ∘-right-id : ∀ {P Q : MP ℓ₁}{F : P ⇒ Q} → F ∘ (id Q) ⇒≡ F
  ∘-right-id p = PropEq.refl

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

-- it's easy to lift predicates to monotone predicates
pack : ∀ {ℓ} → Pred Carrier ℓ → MP _
pack P = mp
  (λ c → ∃ λ c' → c' ∼ c × P c') (record {
    monotone = λ{ c~c' (c'' , c~c'' , pc') → c'' , trans c~c'' c~c' , pc' }
  })

-- the underlying ~ relations is itself a monotone predicate
~mp : ∀ c → IsMP (_∼_ c)
~mp c = record { monotone = flip trans }
