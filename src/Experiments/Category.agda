open import Relation.Binary hiding (_⇒_)

module Experiments.Category {ℓ₁ ℓ₂ ℓ₃} (APO : Preorder ℓ₁ ℓ₂ ℓ₃) where

open import Level
open Preorder APO
open import Function as Fun using (flip)
open import Relation.Unary using (Pred)
open import Data.Product as Prod using (_,_; _×_)
import Relation.Binary.PropositionalEquality as PEq
open PEq.≡-Reasoning
open import Function.Inverse using (Inverse)
open import Algebra.FunctionProperties

record IsMP {ℓ}(P : Carrier → Set ℓ) : Set (ℓ ⊔ ℓ₁ ⊔ ℓ₃) where
  field
    monotone : ∀ {c c'} → c ∼ c' → P c → P c'

    monotone-refl  : ∀ {c} p → monotone (refl {c}) p PEq.≡ p
    monotone-trans : ∀ {c c' c''} p (c~c' : c ∼ c')(c'~c'' : c' ∼ c'') →
                     monotone (trans c~c' c'~c'') p PEq.≡ monotone c'~c'' (monotone c~c' p)

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
P ≗ Q = ∀ {c} → P · c PEq.≡ Q · c

import Data.Unit as Unit

Const : ∀ {ℓ}(P : Set ℓ) → MP ℓ
Const P = mp (λ _ → P) (record {
    monotone = λ x p → p ;
    monotone-refl = λ p → PEq.refl ;
    monotone-trans = λ p c~c' c'~c'' → PEq.refl
  })

⊤ : MP zero
⊤ = Const Unit.⊤

-- we package the Agda function that represents morphisms
-- in this category in a record such that P ⇒ Q doesn't get
-- reduced to the simple underlying type of `apply`
infixl 30 _⇒_
record _⇒_ {p q}(P : MP p)(Q : MP q) : Set (p ⊔ q ⊔ ℓ₁ ⊔ ℓ₃) where
  constructor mk⇒

  field
    apply         : ∀ {c} → P · c → Q · c
    monotone-comm : ∀ {c c'}(c~c' : c ∼ c'){p : P · c} →
                    apply {c'} (MP.monotone P c~c' p) PEq.≡ MP.monotone Q c~c' (apply p)

open _⇒_ public

terminal : ∀ {ℓ a}{A : Set a}{P : MP ℓ} → A → P ⇒ Const A
terminal x = mk⇒ (λ _ → x) λ c~c' → λ {p} → PEq.refl

infixl 100 _∘_
_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃}{P : MP ℓ₁}{Q : MP ℓ₂}{R : MP ℓ₃} → Q ⇒ R → P ⇒ Q → P ⇒ R
_∘_ {P = P}{Q}{R} F G = mk⇒
  (λ p → apply F (apply G p))
  (λ c~c' →
    begin _
      ≡⟨ PEq.cong (λ e → apply F e) (monotone-comm G c~c') ⟩
    apply F (MP.monotone Q c~c' (apply G _))
      ≡⟨ monotone-comm F c~c' ⟩
    _ ∎
  )

id : ∀ {ℓ}(P : MP ℓ) → P ⇒ P
id P = mk⇒ Fun.id (λ _ → PEq.refl)

-- morphism equality
infixl 20 _⇒≡_
_⇒≡_  : ∀ {ℓ₁ ℓ₂}{P : MP ℓ₁}{Q : MP ℓ₂}(F G : P ⇒ Q) → Set _
_⇒≡_ {P = P}{Q} F G = ∀ {c}(p : P · c) → apply F p PEq.≡ apply G p

-- isomorphism
record _≅_ {ℓ}(P Q : MP ℓ) : Set (ℓ₁ ⊔ ℓ ⊔ ℓ₃) where
  field
    to    : P ⇒ Q
    from  : Q ⇒ P
    left-inv  : to ∘ from ⇒≡ id Q
    right-inv : from ∘ to ⇒≡ id P

module Properties where
  ∘-assoc : ∀ {p q r s}{P : MP p}{Q : MP q}{R : MP r}{S : MP s}
              {F : R ⇒ S}{G : Q ⇒ R}{H : P ⇒ Q} →
              F ∘ (G ∘ H) ⇒≡ (F ∘ G) ∘ H
  ∘-assoc _ = PEq.refl

  ∘-left-id : ∀ {P Q : MP ℓ₁}{F : P ⇒ Q} → (id Q) ∘ F ⇒≡ F
  ∘-left-id _ = PEq.refl

  ∘-right-id : ∀ {P Q : MP ℓ₁}{F : P ⇒ Q} → F ∘ (id P) ⇒≡ F
  ∘-right-id p = PEq.refl

module Product where
  -- within the category

  infixl 40 _⊗_
  _⊗_ : ∀ {ℓ₁ ℓ₂} → MP ℓ₁ → MP ℓ₂ → MP (ℓ₁ ⊔ ℓ₂)
  P ⊗ Q = mp
      (λ c → (P · c) × (Q · c))
      (record {
        monotone = λ{ c~c' (p , q) →
            MP.monotone P c~c' p
          , MP.monotone Q c~c' q
        };
        monotone-refl = λ _ → PEq.cong₂ _,_ (MP.monotone-refl P _) (MP.monotone-refl Q _) ;
        monotone-trans = λ _ _ _ → PEq.cong₂ _,_ (MP.monotone-trans P _ _ _) (MP.monotone-trans Q _ _ _)
      })

  ⟨_,_⟩ : ∀ {y p q}{Y : MP y}{P : MP p}{Q : MP q} → Y ⇒ P → Y ⇒ Q → Y ⇒ P ⊗ Q
  ⟨ F , G ⟩ = mk⇒
    (λ x → apply F x , apply G x)
    (λ c~c' → PEq.cong₂ _,_ (monotone-comm F c~c') (monotone-comm G c~c'))

  π₁ : ∀ {ℓ₁ ℓ₂}{P : MP ℓ₁}{Q : MP ℓ₂} → P ⊗ Q ⇒ P
  π₁ = mk⇒ (λ{ (pc , qc) → pc}) (λ c~c' → PEq.refl)

  π₂ : ∀ {ℓ₁ ℓ₂}{P : MP ℓ₁}{Q : MP ℓ₂} → P ⊗ Q ⇒ Q
  π₂ = mk⇒ (λ{ (pc , qc) → qc}) (λ c~c' → PEq.refl)

  swap : ∀ {ℓ₁ ℓ₂}(P : MP ℓ₁)(Q : MP ℓ₂) → P ⊗ Q ⇒ Q ⊗ P
  swap _ _ = mk⇒ Prod.swap λ c~c' → PEq.refl

  fmap : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}{P : MP ℓ₁}{Q : MP ℓ₂}{R : MP ℓ₃}{S : MP ℓ₄} →
         (F : P ⇒ R)(G : Q ⇒ S) → P ⊗ Q ⇒ R ⊗ S
  fmap F G = ⟨ F ∘ π₁ , G ∘ π₂ ⟩

  curry-fun : ∀ {ℓ₁ ℓ₂ ℓ₃}{A : Set ℓ₁}{P : MP ℓ₂}{Q : MP ℓ₃} →
              (A → P ⇒ Q) → (Const A ⊗ P ⇒ Q)
  curry-fun {A = A}{P}{Q} f = mk⇒
    (λ{ (a , p) → apply (f a) p })
    (λ{ c~c' {a , p} → monotone-comm (f a) c~c' })

  module ⊗-Properties where
    π₁-comm : ∀ {y p q}{Y : MP y}{P : MP p}{Q : MP q}{F : Y ⇒ P}{G : Y ⇒ Q} →
            π₁ ∘ ⟨ F , G ⟩ ⇒≡ F
    π₁-comm _ = PEq.refl

    π₂-comm : ∀ {y p q}{Y : MP y}{P : MP p}{Q : MP q}{F : Y ⇒ P}{G : Y ⇒ Q} →
            π₂ ∘ ⟨ F , G ⟩ ⇒≡ G
    π₂-comm _ = PEq.refl

    unique : ∀ {y p q}{Y : MP y}{P : MP p}{Q : MP q}{g : Y ⇒ (P ⊗ Q)} → ⟨ π₁ ∘ g , π₂ ∘ g ⟩ ⇒≡ g
    unique _ = PEq.refl

module Exists where

  -- simple existential quantification for indexed monotone predicates
  Exists : ∀ {ℓ₁ ℓ₂}{I : Set ℓ₁}(P : I → MP ℓ₂) → MP _
  Exists {I = I} P = mp (λ x → Prod.∃ λ (i : I) → P i · x) (record {
      monotone = λ{ c~c' (i , px) → i , MP.monotone (P i) c~c' px } ;
      monotone-refl = λ{
        (i , px) → PEq.cong (λ u → i , u) (MP.monotone-refl (P i) px) };
      monotone-trans = (λ {
        (i , px) p q → PEq.cong (λ u → i , u) (MP.monotone-trans (P i) px p q)})
    })

  elim : ∀ {ℓ₁ ℓ₂ ℓ₃}{I : Set ℓ₁}{P : I → MP ℓ₂}{Q : MP ℓ₃} →
         (∀ {i} → P i ⇒ Q) → Exists P ⇒ Q
  elim {P = P}{Q} F = mk⇒
    (λ{ (i , pi) → apply F pi})
    (λ{ c~c' {(i , pi)} → monotone-comm F c~c' })

module Monoid where
  -- identifies _⊗_ as a tensor/monoidal product
  open Product

  -- associator
  assoc : ∀ {p q r}{P : MP p}{Q : MP q}{R : MP r} →
                  (P ⊗ Q) ⊗ R ≅ P ⊗ (Q ⊗ R)
  assoc = record {
    to = mk⇒ (λ{ ((p , q) , r) → p , (q , r) }) (λ c~c' → PEq.refl) ;
    from = mk⇒ (λ{ (p , (q , r)) → (p , q) , r }) (λ c~c' → PEq.refl) ;
    left-inv = λ _ → PEq.refl ;
    right-inv = λ _ → PEq.refl }

  -- left unitor
  ⊗-left-id : ∀ {p}{P : MP p} → ⊤ ⊗ P ≅ P
  ⊗-left-id = record {
    to = π₂ {P = ⊤} ;
    from = ⟨ mk⇒ (λ x → Unit.tt) (λ c~c' → PEq.refl) , id _ ⟩ ;
    left-inv = λ p → PEq.refl ;
    right-inv = λ p → PEq.refl }

  -- right unitor
  ⊗-right-id : ∀ {p}{P : MP p} → P ⊗ ⊤ ≅ P
  ⊗-right-id = record {
    to = π₁ {Q = ⊤} ;
    from = ⟨ mk⇒ (λ {c} z → z) (λ c~c' → PEq.refl) , mk⇒ (λ {c} _ → Unit.tt) (λ c~c' → PEq.refl) ⟩ ;
    left-inv = λ p → PEq.refl ;
    right-inv = λ p → PEq.refl }

  -- TODO: coherence conditions

module Exponents where

  open Product

  record _^_ {o}(Z : MP o)(Y : MP o) : Set (suc o ⊔ ℓ₃ ⊔ ℓ₁) where
    constructor mk^
    field
      Zʸ   : MP o

      λg  : ∀ (X : MP o)(G : (X ⊗ Y) ⇒ Z) → X ⇒ Zʸ
      apply : Zʸ ⊗ Y ⇒ Z

{-}
-- it's easy to lift predicates to monotone predicates using a product
pack : ∀ {ℓ} → Pred Carrier ℓ → MP _
pack P = mp
  (λ c → ∃ λ c' → c' ∼ c × P c') (record {
    monotone = λ{ c~c' (c'' , c~c'' , pc') → c'' , trans c~c'' c~c' , pc' } ;
    monotone-refl = ? ;
    monotone-trans = ?
  })

-- the underlying ~ relations is itself a monotone predicate
~mp : ∀ c → IsMP (_∼_ c)
~mp c = record {
  monotone = flip trans
  monotone-refl = ? ;
  monotone-trans = ?
  }
-}
