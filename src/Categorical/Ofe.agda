open import Categories.Agda
open import Categories.Support.Equivalence using (Setoid)
import Categories.Support.SetoidFunctions as SF

module Categorical.Ofe where

open import Relation.Binary.Core using (Reflexive; Transitive; Symmetric) renaming (_≡_ to _≣_; refl to ≣-refl)
open import Relation.Binary using (IsEquivalence)
open import Level using (_⊔_) renaming (suc to lsuc)
open import Data.Nat hiding (_⊔_)
open import Data.Product

Fuel = ℕ

record Ofe s₁ s₂ e : Set (lsuc s₁ ⊔ lsuc s₂ ⊔ lsuc e) where
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

_[_≈_] : ∀ {c ℓ e} (O : Ofe c ℓ e) → (x y : Ofe.Carrier O) → Set _
O [ x ≈ y ] = Ofe._≈_ O x y

_[_≋_] : ∀ {c ℓ e} (O : Ofe c ℓ e) → (x y : Ofe.Carrier O) → Set _
O [ x ≋ y ] = Ofe._≋_ O x y

_[_≈⟨_⟩_] : ∀ {c ℓ e} (O : Ofe c ℓ e) → Ofe.Carrier O → Fuel → Ofe.Carrier O → Set _
O [ x ≈⟨ n ⟩ y ] = Ofe._≈⟨_⟩_ O x n y

module OfeReasoning {c ℓ e}(O : Ofe c ℓ e) where
  open Ofe O

  infix  4 _IsRelatedTo⟨_⟩_
  infix  1 begin_
  infixr 2 _↓⟨_⟩_ _↑⟨_⟩_ _↓≣⟨_⟩_ _↑≣⟨_⟩_ _↕_
  infix  3 _∎

  -- This seemingly unnecessary type is used to make it possible to
  -- infer arguments even if the underlying equality evaluates.

  data _IsRelatedTo⟨_⟩_ (x : Carrier) n (y : Carrier) : Set (ℓ ⊔ e) where
    relTo : (x∼y : x ≈⟨ n ⟩ y) → x IsRelatedTo⟨ n ⟩ y

  .begin_ : ∀ {x y n} → x IsRelatedTo⟨ n ⟩ y → x ≈⟨ n ⟩ y
  begin relTo x∼y = x∼y

  ._↓⟨_⟩_ : ∀ x {y z n} → x ≈⟨ n ⟩ y → y IsRelatedTo⟨ n ⟩ z → x IsRelatedTo⟨ n ⟩ z
  _ ↓⟨ x∼y ⟩ relTo y∼z = relTo (≈ₙ-trans x∼y y∼z)

  ._↑⟨_⟩_ : ∀ x {y z n} → y ≈⟨ n ⟩ x → y IsRelatedTo⟨ n ⟩ z → x IsRelatedTo⟨ n ⟩ z
  _ ↑⟨ y∼x ⟩ relTo y∼z = relTo (≈ₙ-trans (≈ₙ-sym y∼x) y∼z)

  ._↓≣⟨_⟩_ : ∀ x {y z n} → x ≣ y → y IsRelatedTo⟨ n ⟩ z → x IsRelatedTo⟨ n ⟩ z
  _ ↓≣⟨ ≣-refl ⟩ y∼z = y∼z

  ._↑≣⟨_⟩_ : ∀ x {y z n} → y ≣ x → y IsRelatedTo⟨ n ⟩ z → x IsRelatedTo⟨ n ⟩ z
  _ ↑≣⟨ ≣-refl ⟩ y∼z = y∼z

  ._↕_ : ∀ x {z n} → x IsRelatedTo⟨ n ⟩ z → x IsRelatedTo⟨ n ⟩ z
  _ ↕ x∼z = x∼z

  ._∎ : ∀ x {n} → x IsRelatedTo⟨ n ⟩ x
  _∎ _ = relTo ≈ₙ-refl

record Chain {s₁ s₂ e}(T : Ofe s₁ s₂ e) : Set (s₁ ⊔ s₂ ⊔ e) where
  open Ofe T
  field
    _at_  : Fuel → Carrier
    .cauchy : ∀ {i j n} → n ≤ i → n ≤ j → _at_ i ≈⟨ n ⟩ _at_ j

open Chain public

-- pointwise equal chains
_chain≈⟨_⟩_ : ∀ {s₁ s₂ e}{A : Ofe s₁ s₂ e} → Chain A → ℕ → Chain A → Set e
_chain≈⟨_⟩_ {A = A} l n r = ∀ i → A [ l at i ≈⟨ n ⟩ r at i ]

-- non-expansive functions
infixr 0 _⟶_
record _⟶_ {cf ℓf ct ℓt ef et} (From : Ofe cf ℓf ef)(To : Ofe ct ℓt et) : Set (cf ⊔ ℓf ⊔ ct ⊔ ℓt ⊔ ef ⊔ et) where
  infixl 5 _⟨$⟩_
  private
    module From = Ofe From
    module To = Ofe To
  field
    _⟨$⟩_ : From.Carrier → To.Carrier
    .cong : ∀ {n x y} → x From.≈⟨ n ⟩ y → _⟨$⟩_ x To.≈⟨ n ⟩ _⟨$⟩_ y

open _⟶_ public

id : ∀ {c f e} → (o : Ofe c f e) → o ⟶ o
_⟨$⟩_ (id o) x = x
cong (id o) x = x

_∘_ : ∀ {c f e c' f' e' c'' f'' e''}{o : Ofe c f e}{o' : Ofe c' f' e'}{o'' : Ofe c'' f'' e''} →
      o' ⟶ o'' → o ⟶ o' → o ⟶ o''
_⟨$⟩_ (_∘_ g f) x = g ⟨$⟩ (f ⟨$⟩ x)
cong (_∘_ g f) x = cong g (cong f x)

-- non-expansive functions preserve cauchyness of chains
chain-map : ∀ {cf ℓf ct ℓt ef et} {From : Ofe cf ℓf ef}{To : Ofe ct ℓt et} →
            (From ⟶ To) → Chain From → Chain To
chain-map f c = record
  { _at_ = λ n → f ⟨$⟩ (c at n)
  ; cauchy = λ n≤i n≤j → cong f (cauchy c n≤i n≤j) }

-- non-expansive functions between ofes form a ofe themselves
_⇨_ : ∀ {cf ℓf ct ℓt ef et} (From : Ofe cf ℓf ef)(To : Ofe ct ℓt et) → Ofe _ _ _
From ⇨ To = record
  { setoid = setoid
  ; _≈⟨_⟩_ = _≈⟨_⟩_
  ; equiv = isEquiv
  ; limit₁ = λ {f}{g} x≈y n → limit₁ f g x≈y n
  ; limit₂ = λ {f}{g} → limit₂ f g
  ; monotone = λ {n n' f g} → monotone f g
  }
  module NE where
    module From = Ofe From
    module To = Ofe To

    _≈⟨_⟩_ : ∀ (f : From ⟶ To) n (g : From ⟶ To) → Set _
    f ≈⟨ n ⟩ g = ∀ {x y} → x From.≈⟨ n ⟩ y → (f ⟨$⟩ x) To.≈⟨ n ⟩ (g ⟨$⟩ y)

    _≈_ = λ (f g : From ⟶ To) → ∀ {x y} → x From.≈ y → (f ⟨$⟩ x) To.≈ (g ⟨$⟩ y)
    _≋_ = λ (f g : From ⟶ To) → ∀ n → f ≈⟨ n ⟩ g

    .limit₁ : ∀ (f g : From ⟶ To) → f ≈ g → f ≋ g
    limit₁ f g f≈g n x≈ₙy = To.≈ₙ-trans (To.limit₁ (f≈g From.≈-refl) n) (cong g x≈ₙy)

    .limit₂ : ∀ (f g : From ⟶ To) → (f ≋ g) → f ≈ g
    limit₂ f g f≋g x≈y = To.limit₂ λ n → f≋g n (From.limit₁ x≈y n)

    .≈-cong : ∀ {x y} → (f : From ⟶ To) → From [ x ≈ y ] → To [ f ⟨$⟩ x ≈ f ⟨$⟩ y ]
    ≈-cong f x≈y = limit₂ f f (λ n x≈ₙy → cong f x≈ₙy) x≈y

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
        { refl  = λ {f} x≈y → ≈-cong f x≈y
        ; sym   = λ f∼g x∼y → To.≈-sym (f∼g (From.≈-sym x∼y))
        ; trans = λ f∼g g∼h x∼y → To.≈-trans (f∼g x∼y) (g∼h From.≈-refl)
        }
      }

    .monotone : ∀ {n n' : ℕ} f g → n ≥ n' → f ≈⟨ n ⟩ g → f ≈⟨ n' ⟩ g
    monotone f g  n≥n' f≈ₙg x≈ₙ'y = To.≈ₙ-trans
      (To.monotone n≥n' (f≈ₙg From.≈ₙ-refl))
      (cong g x≈ₙ'y) -- g x ≈⟨ n' ⟩ g y

open import Categories.Category

Ofes : ∀ {c ℓ e} → Category _ _ _
Ofes {c}{ℓ}{e} = record {
  Obj = Ofe c ℓ e;
  _⇒_ = _⟶_ ;
  _≡_ = λ {o}{o'} → Ofe._≈_ (o ⇨ o') ;
  id  = id _ ;
  _∘_ = _∘_ ;
  assoc = λ {A}{B}{C}{D}{f}{g}{h} x≈y → NE.≈-cong _ _ (h ∘ (g ∘ f)) x≈y ;
  identityʳ = λ {A}{B}{f} x≈y → NE.≈-cong _ _ f x≈y;
  identityˡ = λ {A}{B}{f} x≈y → NE.≈-cong _ _ f x≈y;
  equiv = λ {A}{B} → Ofe.≈equiv (A ⇨ B) ;
  ∘-resp-≡ = λ {_ _ _}{f}{g}{h} f≈g h≈i x≈y → f≈g (h≈i x≈y) }

record Limit {s₁ s₂ e}{o : Ofe s₁ s₂ e}(c : Chain o) : Set (s₁ ⊔ s₂ ⊔ e) where
  constructor lim
  open Ofe o
  field
    at-∞  : Carrier
    .limit : ∀ n → (c at n) ≈⟨ n ⟩ at-∞

open Limit public

.limit-map : ∀ {s₁ s₂ e s₁' s₂' e'}{o : Ofe s₁ s₂ e}{o' : Ofe s₁' s₂' e'}{c : Chain o}(f : o ⟶ o') →
             Limit c → Limit (chain-map f c)
limit-map f (lim c∞ limit) = lim (f ⟨$⟩ c∞) (λ n → cong f (limit n))
