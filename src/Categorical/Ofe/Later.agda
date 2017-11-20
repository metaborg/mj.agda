module Categorical.Ofe.Later where

import Relation.Binary.PropositionalEquality as PEq
open import Categories.Support.Equivalence using (Setoid)
open import Categories.Support.EqReasoning
open import Relation.Binary using (IsEquivalence)
open import Data.Nat
open import Data.Unit hiding (setoid; _≤_)
open import Level

open import Categorical.Ofe renaming (Ofes to Ofes′)
open import Categories.Category
open import Categories.Functor.Core

open Functor
open Category

module Later {s₁ s₂ e}(o : Ofe s₁ s₂ e) where
  open Ofe o

  data Later : Set s₁ where
    next : Carrier → Later

  data _later≈_ : Later → Later → Set s₂ where
    next : ∀ {x x'} → x ≈ x' → (next x) later≈ (next x')

  unnext : ∀ {x y} → (next x) later≈ (next y) → x ≈ y
  unnext (next eq) = eq

  .≈-equiv : IsEquivalence _later≈_
  ≈-equiv = record
    { refl = λ{ {next x} → next ≈-refl }
    ; sym  = λ{ (next x≈y) → next (≈-sym x≈y) }
    ; trans = λ{ (next x≈y) (next y≈z) → next (≈-trans x≈y y≈z) }}

  data _later≈⟨_⟩_ : Later → Fuel → Later → Set e where
    now   : ∀ {x y} → x later≈⟨ ℕ.zero ⟩ y
    next  : ∀ {x y n} → x ≈⟨ n ⟩ y → (next x) later≈⟨ ℕ.suc n ⟩ (next y)

  unnextₙ : ∀ {x y n} → (next x) later≈⟨ ℕ.suc n ⟩ (next y) → x ≈⟨ n ⟩ y
  unnextₙ (next eq) = eq

  oid : Setoid _ _
  oid = record
    { Carrier = Later
    ; _≈_ = _later≈_
    ; isEquivalence = ≈-equiv }

-- it is a functor in the category of Ofes
module LaterOfe {s₁ s₂ e} where
  Ofes = Ofes′ s₁ s₂ e

  omap : (T : Ofe s₁ s₂ e) → Ofe _ _ _
  omap T = record
    { setoid = oid
    ; _≈⟨_⟩_ = _later≈⟨_⟩_
    ; equiv = λ {n} → ≈ₙequiv {n}
    ; limit₁ = limit₁'
    ; limit₂ = limit₂'
    ; monotone = mono
    }
    where
      open Ofe T
      open Later T

      .limit₁' : ∀ {x y} → Setoid._≈_ oid x y → (n : ℕ) → x later≈⟨ n ⟩ y
      limit₁' (next x) ℕ.zero = now
      limit₁' (next x) (ℕ.suc n) = next (Ofe.limit₁ T x n)

      open IsEquivalence
      .≈ₙequiv : ∀ {n} → IsEquivalence (λ x y → x later≈⟨ n ⟩ y)
      refl (≈ₙequiv {n}) = limit₁' (Setoid.refl oid) n
      sym ≈ₙequiv now = now
      sym ≈ₙequiv (next x≈ₙy) = next (Ofe.≈ₙ-sym T x≈ₙy)
      trans ≈ₙequiv now now = now
      trans ≈ₙequiv (next x≈ₙy) (next y≈ₙz) = next (Ofe.≈ₙ-trans T x≈ₙy y≈ₙz)

      .limit₂' : ∀ {x y} → ((n : ℕ) → x later≈⟨ n ⟩ y) → (x later≈ y)
      limit₂' {next x} {next y} x≋y = next (limit₂ λ n → unnextₙ (x≋y (ℕ.suc n)))

      .mono : ∀ {n n' : ℕ} {x y} → n' ≤ n → x later≈⟨ n ⟩ y → x later≈⟨ n' ⟩ y
      mono z≤n x≈ₙy = now
      mono (s≤s le) (next x≈ₙy) = next (monotone le x≈ₙy)

  open Later

  next-ne : ∀ (A : Obj Ofes) → Ofes [ A , omap A ]
  _⟨$⟩_ (next-ne _) x = next x
  cong (next-ne _) {ℕ.zero} {x} {y} eq = now
  cong (next-ne A) {ℕ.suc n} {x} {y} eq = next (Ofe.monotone A (n≤1+n n) eq)
    where open import Data.Nat.Properties

  next-map : ∀ {A B} → Ofes [ A , B ] → Ofe.Carrier (omap A) → Ofe.Carrier (omap B)
  next-map F (next x) = next (F ⟨$⟩ x)

  hmap : ∀ {A B} → Ofes [ A , B ] → Ofes [ omap A , omap B ]
  hmap {A = A}{B} F = record
    { _⟨$⟩_ = next-map F
    ; cong  = λ{ now → now ; (next eq) → next (cong F eq) }}

  .homomorph : ∀ {X Y Z}{f : Ofes [ X , Y ]}{g : Ofes [ Y , Z ]} →
               Ofes [ hmap (Ofes [ g ∘ f ]) ≡ Ofes [ hmap g ∘ hmap f ] ]
  homomorph {X = X} {Y} {Z} {f} {g} {next x} {next y} x≈y =
    begin
      hmap (Ofes [ g ∘ f ]) ⟨$⟩ (next x)
    ↓⟨ NE.≈-cong _ _ (hmap (Ofes [ g ∘ f ])) x≈y ⟩
      hmap (Ofes [ g ∘ f ]) ⟨$⟩ (next y)
    ↓≣⟨ PEq.refl ⟩
      Ofes [ hmap g ∘ hmap f ] ⟨$⟩ (next y)
    ∎
    where open SetoidReasoning (Ofe.setoid (omap Z))

  .identity′ : ∀ {A} → Ofes [ hmap {A = A} (Category.id Ofes) ≡ Category.id Ofes ]
  identity′ {A} {x = next x}{next y} x≈y =
    begin
      hmap (Category.id Ofes) ⟨$⟩ (next x)
    ↓≣⟨ PEq.refl ⟩
      (next x)
    ↓⟨ x≈y ⟩
      (next y)
    ∎
    where open SetoidReasoning (Ofe.setoid (omap A))

  .resp : ∀ {A B}{F G : Ofes [ A , B ]} → Ofes [ F ≡ G ] → Ofes [ hmap F ≡ hmap G ]
  resp {A}{B}{F}{G} F≡G {x = next x}{next y} x≈y =
    begin
      next (F ⟨$⟩ x)
    ↓⟨ NE.≈-cong _ _ (next-ne B) (F≡G (Ofe.≈-refl A)) ⟩
      next (G ⟨$⟩ x)
    ↓⟨ NE.≈-cong _ _ (hmap G) x≈y ⟩
      hmap G ⟨$⟩ (next y)
    ∎
    where open SetoidReasoning (Ofe.setoid (omap B))

  functor : Endofunctor Ofes
  F₀ functor = omap
  F₁ functor = hmap
  homomorphism functor = homomorph
  identity functor = identity′
  F-resp-≡ functor = resp

open LaterOfe using () renaming (functor to ►) public
