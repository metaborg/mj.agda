open import Categories.Support.Equivalence

-- A category of *set-indexed* setoids (≡ predicates over a Set) module Categorical.Predicates {s₁}(S : Set s₁) where

open import Level

open import Data.Product
open import Relation.Binary using (IsPreorder) renaming (Preorder to Po)
open import Relation.Binary.PropositionalEquality as PEq using () renaming (_≡_ to _≣_)

open import Categories.Category
open import Categories.Functor using (Functor; Endofunctor) renaming (id to 𝕀; _∘_ to _F∘_)
open import Categories.Support.SetoidFunctions as SF hiding (id)
open import Categories.Support.EqReasoning

open Category
open Functor
open Setoid

_[_≈_] : ∀ {s₁ s₂} (S : Setoid s₁ s₂) → Carrier S → Carrier S → Set _
_[_≈_] = Setoid._≈_

Pred : ∀ s₁ s₂ → Category _ _ _
Obj (Pred s₁ s₂) = (c : S) → Setoid s₁ s₂
_⇒_ (Pred s₁ s₂) T S = ∀ {Σ} → (T Σ) ⟶ (S Σ)
_≡_ (Pred s₁ s₂) {A}{B} f g = ∀ {Σ}{x : Carrier (A Σ)} → Setoid._≈_ (B Σ) (f ⟨$⟩ x) (g ⟨$⟩ x)
id (Pred s₁ s₂) = SF.id
_∘_ (Pred s₁ s₂) f g = f ∙ g
assoc (Pred s₁ s₂) {A} {B} {C} {D} = Setoid.refl (D _)
identityˡ (Pred s₁ s₂) {A} {B} = Setoid.refl (B _)
identityʳ (Pred s₁ s₂) {A} {B} = Setoid.refl (B _)
equiv (Pred s₁ s₂) {A}{B} = record
    { refl = Setoid.refl (B _)
    ; sym = λ eq → sym (B _) eq
    ; trans = λ eq₁ eq₂ → Setoid.trans (B _) eq₁ eq₂ }
∘-resp-≡ (Pred s₁ s₂) {A}{B}{C}{f}{g}{h}{i} f≡g h≡i {Σ}{x} =
  begin
      f ⟨$⟩ (h ⟨$⟩ x)
    ↓⟨ cong f h≡i ⟩
      f ⟨$⟩ (i ⟨$⟩ x)
    ↓⟨ f≡g ⟩
      g ⟨$⟩ (i ⟨$⟩ x) ∎
  where open SetoidReasoning (C Σ)

Pred' : ∀ {s₁ s₂} → Category _ _ _
Pred' {s₁} {s₂} = Pred s₁ s₂

-- lift equality indexed-setoid into a heterogeneous equality type
data _[_≅_] {s₁ s₂}(I : Obj (Pred s₁ s₂)) {c} : ∀ {c'} → Carrier (I c) → Carrier (I c') → Set (s₁ ⊔ s₂) where
  hrefl : ∀ {l r} → (I c) [ l ≈ r ] → I [ l ≅ r ]

.≅cong : ∀ {s₁ s₂}{I J : Obj (Pred s₁ s₂)}
          {l l'}{r : Carrier (I l)}{r' : Carrier (I l')} →
          (f : Pred' [ I , J ]) → I [ r ≅ r' ] → J [ (f ⟨$⟩ r) ≅ (f ⟨$⟩ r') ]
≅cong f (hrefl x) = (hrefl (cong f x))

∃[_]-setoid_ : ∀ {ℓ s₁ s₂} → (A : Set ℓ) → Obj (Pred s₁ s₂) → Setoid _ _
∃[ A ]-setoid B = record
  { Carrier = ∃ λ a → B.Carrier a
  ; _≈_ = λ p q → B [ (proj₂ p) ≅ (proj₂ q) ]
  ; isEquivalence = record {
    refl = λ {x} → hrefl (Setoid.refl (B (proj₁ x))) ;
    sym = λ{ {i}{j}(hrefl p) → hrefl (Setoid.sym (B (proj₁ j)) p) };
    trans = λ{ (hrefl p) (hrefl q) → hrefl (Setoid.trans (B _) p q) }}
  }
  where module B a = Setoid (B a)
