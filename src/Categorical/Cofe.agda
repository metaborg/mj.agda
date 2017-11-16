open import Categories.Agda
open import Categories.Support.Equivalence using (Setoid)
import Categories.Support.SetoidFunctions as SF

module Categorical.Cofe where

open import Relation.Binary.Core using (Reflexive; Transitive; Symmetric)
open import Relation.Binary using (IsEquivalence)
open import Level using (_⊔_) renaming (suc to lsuc)
open import Data.Nat hiding (_⊔_)
open import Data.Product

Fuel = ℕ

Chain : ∀ {ℓ} → Set ℓ → Set ℓ
Chain T = Fuel → T

record Cofe s₁ s₂ e : Set (lsuc s₁ ⊔ lsuc s₂ ⊔ lsuc e) where
  field
    setoid : Setoid s₁ s₂

  -- TODO open more, renaming stuff
  open Setoid setoid public using (Carrier; _≈_) renaming (reflexive to ≡-reflexive; isEquivalence to ≈equiv)

  field
    -- An approximation of equality
    _≈⟨_⟩_     : Carrier → Fuel → Carrier → Set e

  _≋_ : Carrier → Carrier → Set e
  x ≋ y = ∀ n → x ≈⟨ n ⟩ y

  field
    -- ...which is an equivalence for every level op approximation,
    .equiv      : ∀ {n} → IsEquivalence (λ x y → x ≈⟨ n ⟩ y)
    -- ...respects the setoid equivalence,
    .limit₁      : ∀ {x y} → x ≈ y → x ≋ y
    .limit₂      : ∀ {x y} → x ≋ y → x ≈ y
    -- ...an is monotone
    .monotone   : ∀ {n n' x y} → n ≥ n' → x ≈⟨ n ⟩ y → x ≈⟨ n' ⟩ y

  Cauchy : Chain Carrier → Set _
  Cauchy c = ∀ {i j n} → n ≤ i → n ≤ j → c i ≈⟨ n ⟩ c j

  field
    -- completeness := every cauchy chain of carriers has a limit
    .complete : ∀ {c : Chain Carrier} → Cauchy c → ∃ λ (c∞ : Carrier) → ∀ n → c n ≈⟨ n ⟩ c∞

  -- no irrelevant opens
  .≈-sym : Symmetric _≈_
  ≈-sym = IsEquivalence.sym ≈equiv
  .≈-trans : Transitive _≈_
  ≈-trans = IsEquivalence.trans ≈equiv
  .≈-refl : Reflexive _≈_
  ≈-refl = IsEquivalence.refl ≈equiv

  .≈ₙ-sym : ∀ {n} → Symmetric (λ x y → x ≈⟨ n ⟩ y)
  ≈ₙ-sym = IsEquivalence.sym equiv
  .≈ₙ-trans : ∀ {n} → Transitive (λ x y → x ≈⟨ n ⟩ y)
  ≈ₙ-trans = IsEquivalence.trans equiv
  .≈ₙ-refl : ∀ {n} → Reflexive (λ x y → x ≈⟨ n ⟩ y)
  ≈ₙ-refl = IsEquivalence.refl equiv

-- non-expansive functions
infixr 0 _⟶_
record _⟶_ {cf ℓf ct ℓt ef et} (From : Cofe cf ℓf ef)(To : Cofe ct ℓt et) : Set (cf ⊔ ℓf ⊔ ct ⊔ ℓt ⊔ ef ⊔ et) where
  infixl 5 _⟨$⟩_
  private
    module From = Cofe From
    module To = Cofe To
  field
    _⟨$⟩_ : From.Carrier → To.Carrier
    .cong : ∀ {n x y} → x From.≈⟨ n ⟩ y → _⟨$⟩_ x To.≈⟨ n ⟩ _⟨$⟩_ y

open _⟶_ public

-- non-expansive functions between cofes form a cofe themselves
_⇨_ : ∀ {cf ℓf ct ℓt ef et} (From : Cofe cf ℓf ef)(To : Cofe ct ℓt et) → Cofe _ _ _
From ⇨ To = record
  { setoid = setoid
  ; _≈⟨_⟩_ = _≈⟨_⟩_
  ; equiv = isEquiv
  ; limit₁ = λ {f}{g} x≈y n → limit₁ f g x≈y n
  ; limit₂ = λ {f}{g} → limit₂ f g
  ; monotone = {!!}
  ; complete = {!!}
  }
  where
    module From = Cofe From
    module To = Cofe To

    _≈⟨_⟩_ : ∀ (f : From ⟶ To) n (g : From ⟶ To) → Set _
    f ≈⟨ n ⟩ g = ∀ {x y} → x From.≈⟨ n ⟩ y → (f ⟨$⟩ x) To.≈⟨ n ⟩ (g ⟨$⟩ y)

    _≈_ = λ (f g : From ⟶ To) → ∀ {x y} → x From.≈ y → (f ⟨$⟩ x) To.≈ (g ⟨$⟩ y)
    _≋_ = λ (f g : From ⟶ To) → ∀ n → f ≈⟨ n ⟩ g

    .limit₁ : ∀ (f g : From ⟶ To) → f ≈ g → f ≋ g
    limit₁ f g f≈g n x≈ₙy = To.≈ₙ-trans (To.limit₁ (f≈g From.≈-refl) n) (cong g x≈ₙy)

    .limit₂ : ∀ (f g : From ⟶ To) → (f ≋ g) → f ≈ g
    limit₂ f g f≋g x≈y = To.limit₂ λ n → f≋g n (From.limit₁ x≈y n)

    open IsEquivalence
    .isEquiv : ∀ {n : ℕ} → IsEquivalence (λ x → _≈⟨_⟩_ x n)
    refl (isEquiv {n}) {F} x≈ₙy = cong F x≈ₙy
    trans (isEquiv {n}) i≈ₙj j≈ₙk x≈ₙy = To.≈ₙ-trans (i≈ₙj x≈ₙy) (j≈ₙk From.≈ₙ-refl)
    sym (isEquiv {n}) i≈ₙj x≈ₙy = To.≈ₙ-sym (i≈ₙj (From.≈ₙ-sym x≈ₙy))

    setoid : Setoid _ _
    setoid = record
      { Carrier       = From ⟶ To
      ; _≈_           = _≈_
      ; isEquivalence = record
        { refl  = λ {f} x≈y → limit₂ f f (λ n x≈ₙy → cong f x≈ₙy) x≈y
        ; sym   = λ f∼g x∼y → To.≈-sym (f∼g (From.≈-sym x∼y))
        ; trans = λ f∼g g∼h x∼y → To.≈-trans (f∼g x∼y) (g∼h From.≈-refl)
        }
      }

id : ∀ {c ℓ e} → (A : Cofe c ℓ e) → A ⟶ A
id = {!!}

open import Categories.Category

Cofes : ∀ {c ℓ e} → Category _ _ _
Cofes {c}{ℓ}{e} = record {
  Obj = Cofe c ℓ e;
  _⇒_ = _⟶_ ;
  _≡_ = λ {A}{B} F G → Cofe._≋_ (A ⇨ B) F G ;
  id  = id _ ;
  _∘_ = {!!} ;
  assoc = {!!} ;
  identityʳ = {!!} ;
  identityˡ = {!!} ;
  equiv = {!!} ;
  ∘-resp-≡ = {!!} }
