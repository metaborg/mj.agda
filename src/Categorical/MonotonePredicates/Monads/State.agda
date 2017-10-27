open import Categorical.Preorder

module Categorical.MonotonePredicates.Monads.State {ℓ}
  (po : PreorderPlus ℓ ℓ ℓ)
  (Store : PreorderPlus.Carrier po → Set ℓ) where

open import Categorical.MonotonePredicates po
open PreorderPlus po hiding (po)

open import Level

open import Data.Product
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality as PEq using () renaming (_≡_ to _≣_)
open import Relation.Binary.HeterogeneousEquality as HEq using () renaming (_≅_ to _≡~_)

open import Categories.Category
open import Categories.Agda
open import Categories.Functor hiding (_≡_; assoc; identityˡ; identityʳ)
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.Monad
open import Categories.Monad.Strong
open import Categories.Support.Equivalence
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Support.SetoidFunctions

open NaturalTransformation using (η; commute)
open Category

private
  module MP = Category MP

-- lift equality from a set-indexed setoid into a heterogeneous equality type
data _[_∼_∼_] {a s₁ s₂}{A : Set a}(I : A → Setoid s₁ s₂){c} :
  ∀ {c'} → Setoid.Carrier (I c) → c ≣ c' → Setoid.Carrier (I c') → Set (a ⊔ s₁ ⊔ s₂) where
  hrefl : ∀ {l r} → Setoid._≈_ (I c) l r → I [ l ∼ PEq.refl ∼ r ]

.cong-∃ : ∀
          {a s₁ s₂}{A : Set a}{I : A → Setoid s₁ s₂}{J : A → Setoid s₁ s₂}
          {l l'}{r : Setoid.Carrier (I l)}{r' : Setoid.Carrier (I l')} →
          (f : ∀ {l} → (I l) ⟶ (J l)) →
          (∃ λ (p : l ≣ l') → I [ r ∼ p ∼ r' ]) →
          ∃ λ (p : l ≣ l') → J [ (f ⟨$⟩ r) ∼ p ∼ (f ⟨$⟩ r') ]
cong-∃ f (PEq.refl , hrefl x) = PEq.refl , (hrefl (cong f x))

∃[_]-setoid_ : ∀ {ℓ s₁ s₂} → (A : Set ℓ) → (A → Setoid s₁ s₂) → Setoid _ _
∃[ A ]-setoid B = record
   { Carrier = ∃ λ a → B.Carrier a
   ; _≈_ = λ p q → ∃ λ (eq : (proj₁ p) ≣ (proj₁ q)) → B [ (proj₂ p) ∼ eq ∼ (proj₂ q) ]
   ; isEquivalence = record {
     refl = λ {x} → PEq.refl , hrefl (Setoid.refl (B (proj₁ x))) ;
     sym = λ{ {i}{j}(PEq.refl , hrefl p) → PEq.refl , hrefl (Setoid.sym (B (proj₁ j)) p) };
     trans = λ{ (PEq.refl , hrefl p) (PEq.refl , hrefl q) → PEq.refl , hrefl (Setoid.trans (B _) p q) }}
   }
  where
    module B a = Setoid (B a)

module State where

  C = op (Preorder po)

  -- Morally : (X ≤ Y × State Y) × P Y
  -- This isn't a monotone predicate... (I think it's anti-monotone in X) -- Arjen
  Result : ∀ {s₁ s₂} → Carrier → (P : Carrier → Setoid s₁ s₂) → Carrier → Setoid _ _
  Result X P Y = (set→setoid (C [ X , Y ] × Store Y)) ×-setoid (P Y)

  -- But it should be an endofunctor of carrier indexed setoids.
  -- It suffices for now that we can map over the inner setoid carrier with a setoid function.
  result-map : ∀ {s₁ s₂}{X Y : Carrier}(P : Carrier → Setoid s₁ s₂)(Q : Carrier → Setoid s₁ s₂) →
               (f : ∀ Y → (P Y) ⟶ (Q Y)) → Result X P Y ⟶ Result X Q Y
  result-map {X}{Y} P Q f = record
    { _⟨$⟩_ = λ x → proj₁ x , (f _) ⟨$⟩ (proj₂ x)
    ; cong = λ x → (proj₁ x) , cong (f _) (proj₂ x) }

  omap : (P : MP.Obj) → MP.Obj
  omap P = ∀[ StateFun ]
    module omap where
      module P = Functor P

      -- fmap-result : ∀ {X} → (MP [ A ⇒ B ])
      StateFun : Carrier → Setoid ℓ ℓ
      StateFun X =
        ∀[ Store X ]-setoid λ μ →
        ∃[ Carrier ]-setoid (Result X P.F₀)

  hmap : ∀ {A B : MP.Obj} → MP [ A , B ] → MP [ omap A , omap B ]
  _⟨$⟩_ (η (hmap A⇒B) X) φ C X⇒C μ =
    let v = φ _ X⇒C μ ; C' = proj₁ v in C' , proj₁ (proj₂ v) , (η A⇒B C') ⟨$⟩ (proj₂ (proj₂ v))
  cong (η (hmap {A}{B} A⇒B) X) φ≡φ' C X⇒C μ = cong-∃ (result-map (Functor.F₀ A) (Functor.F₀ B) (η A⇒B)) (φ≡φ' C X⇒C μ)
  commute (hmap A⇒B) = {!!}

open Monad
St : Monad MP
F St = record {
    F₀ = State.omap
  ; F₁ = State.hmap
  ; identity = {!!}
  ; homomorphism = {!!}
  ; F-resp-≡ = {!!} }
η St = {!!}
μ St = {!!}
assoc St = {!!}
identityˡ St = {!!}
identityʳ St = {!!}
