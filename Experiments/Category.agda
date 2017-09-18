open import Relation.Binary hiding (_⇒_)

module Experiments.Category {ℓ₁ ℓ₂ ℓ₃} (APO : Preorder ℓ₁ ℓ₂ ℓ₃) where

open import Level
open Preorder APO
open import Function as Fun using (flip)
open import Relation.Unary using (Pred)
open import Data.Product
import Relation.Binary.PropositionalEquality as PropEq
open PropEq.≡-Reasoning
open import Function.Inverse using (Inverse)

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

import Data.Unit as Unit
⊤ : MP zero
⊤ = mp (λ _ → Unit.⊤) (record { monotone = λ {c} {c'} _ _ → Unit.tt })

-- we package the Agda function that represents morphisms
-- in this category in a record such that P ⇒ Q doesn't get
-- reduced to the simple underlying type of `apply`
infixl 30 _⇒_
record _⇒_ {p q}(P : MP p)(Q : MP q) : Set (p ⊔ q ⊔ ℓ₁) where
  constructor mk⇒
  field
    apply : ∀ {c} → P · c → Q · c

open _⇒_

infixl 100 _∘_
_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃}{P : MP ℓ₁}{Q : MP ℓ₂}{R : MP ℓ₃} → Q ⇒ R → P ⇒ Q → P ⇒ R
F ∘ G = mk⇒ λ p → apply F (apply G p)

id : ∀ {ℓ}(P : MP ℓ) → P ⇒ P
id P = mk⇒ Fun.id

-- morphism equality
infixl 20 _⇒≡_
_⇒≡_  : ∀ {ℓ₁ ℓ₂}{P : MP ℓ₁}{Q : MP ℓ₂}(F G : P ⇒ Q) → Set _
_⇒≡_ {P = P}{Q} F G = ∀ {c}(p : P · c) → apply F p PropEq.≡ apply G p

-- isomorphism
record _≅_ {ℓ}(P Q : MP ℓ) : Set (ℓ₁ ⊔ ℓ) where
  field
    to    : P ⇒ Q
    from  : Q ⇒ P
    left-inv  : to ∘ from ⇒≡ id Q
    right-inv : from ∘ to ⇒≡ id P

module Properties where
  ∘-assoc : ∀ {p q r s}{P : MP p}{Q : MP q}{R : MP r}{S : MP s}
              {F : R ⇒ S}{G : Q ⇒ R}{H : P ⇒ Q} →
              F ∘ (G ∘ H) ⇒≡ (F ∘ G) ∘ H
  ∘-assoc _ = PropEq.refl

  ∘-left-id : ∀ {P Q : MP ℓ₁}{F : P ⇒ Q} → (id Q) ∘ F ⇒≡ F
  ∘-left-id _ = PropEq.refl

  ∘-right-id : ∀ {P Q : MP ℓ₁}{F : P ⇒ Q} → F ∘ (id P) ⇒≡ F
  ∘-right-id p = PropEq.refl

module Product where

  infixl 40 _⊗_
  _⊗_ : ∀ {ℓ₁ ℓ₂} → MP ℓ₁ → MP ℓ₂ → MP (ℓ₁ ⊔ ℓ₂)
  P ⊗ Q = mp
      (λ c → (P · c) × (Q · c))
      (record {
        monotone = λ{ c~c' (p , q) →
            MP.monotone P c~c' p
          , MP.monotone Q c~c' q
        }
      })

  ⟨_,_⟩ : ∀ {y p q}{Y : MP y}{P : MP p}{Q : MP q} → Y ⇒ P → Y ⇒ Q → Y ⇒ P ⊗ Q
  ⟨ F , G ⟩ = mk⇒ (λ x → apply F x , apply G x)

  π₁ : ∀ {ℓ₁ ℓ₂}{P : MP ℓ₁}{Q : MP ℓ₂} → P ⊗ Q ⇒ P
  π₁ = mk⇒ (λ{ (pc , qc) → pc})

  π₂ : ∀ {ℓ₁ ℓ₂}{P : MP ℓ₁}{Q : MP ℓ₂} → P ⊗ Q ⇒ Q
  π₂ = mk⇒ (λ{ (pc , qc) → qc})

  module ⊗-Properties where
    π₁-comm : ∀ {y p q}{Y : MP y}{P : MP p}{Q : MP q}{F : Y ⇒ P}{G : Y ⇒ Q} →
            π₁ ∘ ⟨ F , G ⟩ ⇒≡ F
    π₁-comm _ = PropEq.refl

    π₂-comm : ∀ {y p q}{Y : MP y}{P : MP p}{Q : MP q}{F : Y ⇒ P}{G : Y ⇒ Q} →
            π₂ ∘ ⟨ F , G ⟩ ⇒≡ G
    π₂-comm _ = PropEq.refl

    unique : ∀ {y p q}{Y : MP y}{P : MP p}{Q : MP q}{g : Y ⇒ (P ⊗ Q)} → ⟨ π₁ ∘ g , π₂ ∘ g ⟩ ⇒≡ g
    unique _ = PropEq.refl

module Monoid where
  -- identifies _⊗_ as a tensor/monoidal product
  open Product

  -- associator
  assoc : ∀ {p q r}{P : MP p}{Q : MP q}{R : MP r} →
                  (P ⊗ Q) ⊗ R ≅ P ⊗ (Q ⊗ R)
  assoc = record {
    to = mk⇒ (λ{ ((p , q) , r) → p , (q , r) }) ;
    from = mk⇒ (λ{ (p , (q , r)) → (p , q) , r }) ;
    left-inv = λ _ → PropEq.refl ;
    right-inv = λ _ → PropEq.refl }

  -- left unitor
  ⊗-left-id : ∀ {p}{P : MP p} → ⊤ ⊗ P ≅ P
  ⊗-left-id = record {
    to = π₂ ;
    from = ⟨ mk⇒ (λ x → Unit.tt) , id _ ⟩ ;
    left-inv = λ p → PropEq.refl ;
    right-inv = λ p → PropEq.refl }

  -- right unitor
  ⊗-right-id : ∀ {p}{P : MP p} → P ⊗ ⊤ ≅ P
  ⊗-right-id = record {
    to = π₁ ;
    from = ⟨ mk⇒ (λ {c} z → z) , mk⇒ (λ {c} _ → Unit.tt) ⟩ ;
    left-inv = λ p → PropEq.refl ;
    right-inv = λ p → PropEq.refl }

-- it's easy to lift predicates to monotone predicates using the product
pack : ∀ {ℓ} → Pred Carrier ℓ → MP _
pack P = mp
  (λ c → ∃ λ c' → c' ∼ c × P c') (record {
    monotone = λ{ c~c' (c'' , c~c'' , pc') → c'' , trans c~c'' c~c' , pc' }
  })

-- the underlying ~ relations is itself a monotone predicate
~mp : ∀ c → IsMP (_∼_ c)
~mp c = record { monotone = flip trans }
