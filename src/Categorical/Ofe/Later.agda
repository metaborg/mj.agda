module Categorical.Ofe.Later where

import Relation.Binary.PropositionalEquality as PEq
open import Categories.Support.Equivalence using (Setoid)
open import Categories.Support.EqReasoning
open import Relation.Binary using (IsEquivalence)
open import Data.Nat
open import Data.Product
open import Data.Unit hiding (setoid; _≤_)
open import Level

open import Categorical.Ofe
open import Categories.Category
open import Categories.Functor.Core

open Functor
open Category

module Later {s₁ s₂ e}(o : Ofe s₁ s₂ e) where
  open Ofe o

  data _later≈⟨_⟩_ : Carrier → Fuel → Carrier → Set e where
    now   : ∀ {x y} → x later≈⟨ ℕ.zero ⟩ y
    next  : ∀ {x y n} → x ≈⟨ n ⟩ y → x later≈⟨ ℕ.suc n ⟩ y

  unnextₙ : ∀ {x y n} → x later≈⟨ ℕ.suc n ⟩ y → x ≈⟨ n ⟩ y
  unnextₙ (next eq) = eq

-- it is a functor in the category of Ofes
module LaterOfe {s₁ s₂ e} where
  omap : (T : Ofe s₁ s₂ e) → Ofe _ _ _
  omap T = record
    { setoid = setoid
    ; _≈⟨_⟩_ = _later≈⟨_⟩_
    ; equiv = λ {n} → ≈ₙequiv {n}
    ; limit₁ = limit₁'
    ; limit₂ = limit₂'
    ; monotone = mono
    }
    where
      open Ofe T
      open Later T

      .limit₁' : ∀ {x y} → x ≈ y → (n : ℕ) → x later≈⟨ n ⟩ y
      limit₁' x ℕ.zero = now
      limit₁' x (ℕ.suc n) = next (Ofe.limit₁ T x n)

      open IsEquivalence
      .≈ₙequiv : ∀ {n} → IsEquivalence (λ x y → x later≈⟨ n ⟩ y)
      refl (≈ₙequiv {n}) = limit₁' ≈-refl n
      sym ≈ₙequiv now = now
      sym ≈ₙequiv (next x≈ₙy) = next (Ofe.≈ₙ-sym T x≈ₙy)
      trans ≈ₙequiv now now = now
      trans ≈ₙequiv (next x≈ₙy) (next y≈ₙz) = next (Ofe.≈ₙ-trans T x≈ₙy y≈ₙz)

      .limit₂' : ∀ {x y} → ((n : ℕ) → x later≈⟨ n ⟩ y) → (x ≈ y)
      limit₂' {x} {y} x≋y = limit₂ λ n → unnextₙ (x≋y (ℕ.suc n))

      .mono : ∀ {n n' : ℕ} {x y} → n' ≤ n → x later≈⟨ n ⟩ y → x later≈⟨ n' ⟩ y
      mono z≤n x≈ₙy = now
      mono (s≤s le) (next x≈ₙy) = next (monotone le x≈ₙy)

  open Later

  next-ne : ∀ (A : Obj Ofes) → Ofes [ A , omap A ]
  _⟨$⟩_ (next-ne _) x = x
  cong (next-ne _) {ℕ.zero} {x} {y} eq = now
  cong (next-ne A) {ℕ.suc n} {x} {y} eq = next (Ofe.monotone A (n≤1+n n) eq)
    where open import Data.Nat.Properties

  hmap : ∀ {A B} → Ofes [ A , B ] → Ofes [ omap A , omap B ]
  hmap {A = A}{B} F = record
    { _⟨$⟩_ = _⟨$⟩_ F
    ; cong  = λ{ now → now ; (next eq) → next (cong F eq) }}

  .homomorph : ∀ {X Y Z}{f : Ofes [ X , Y ]}{g : Ofes [ Y , Z ]} →
               Ofes [ hmap (Ofes [ g ∘ f ]) ≡ Ofes [ hmap g ∘ hmap f ] ]
  homomorph {X = X} {Y} {Z} {f} {g} {x} {y} x≈y =
    begin
      hmap (Ofes [ g ∘ f ]) ⟨$⟩ x
    ↓⟨ NE.≈-cong _ _ (hmap (Ofes [ g ∘ f ])) x≈y ⟩
      hmap (Ofes [ g ∘ f ]) ⟨$⟩ y
    ↓≣⟨ PEq.refl ⟩
      Ofes [ hmap g ∘ hmap f ] ⟨$⟩ y
    ∎
    where open SetoidReasoning (Ofe.setoid (omap Z))

  .identity′ : ∀ {A} → Ofes [ hmap {A = A} (Category.id Ofes) ≡ Category.id Ofes ]
  identity′ {A} {x = x}{y} x≈y =
    begin
      x
    ↓≣⟨ PEq.refl ⟩
      x
    ↓⟨ x≈y ⟩
      y
    ∎
    where open SetoidReasoning (Ofe.setoid (omap A))

  .resp : ∀ {A B}{F G : Ofes [ A , B ]} → Ofes [ F ≡ G ] → Ofes [ hmap F ≡ hmap G ]
  resp {A}{B}{F}{G} F≡G {x = x}{y} x≈y =
    begin
      F ⟨$⟩ x
    ↓⟨ NE.≈-cong _ _ (next-ne B) (F≡G (Ofe.≈-refl A)) ⟩
      G ⟨$⟩ x
    ↓⟨ NE.≈-cong _ _ (hmap G) x≈y ⟩
      hmap G ⟨$⟩ y
    ∎
    where open SetoidReasoning (Ofe.setoid (omap B))

  functor : Endofunctor Ofes
  F₀ functor = omap
  F₁ functor = hmap
  homomorphism functor {f = f}{g} x = homomorph {f = f}{g} x
  identity functor {A} = identity′ {A}
  F-resp-≡ functor {F = F}{G} = resp {F = F}{G}

open LaterOfe using (next-ne) renaming (functor to ►F; omap to ►; hmap to fmap) public

Contractive : ∀ {s₁ s₂ e}{A B : Ofe s₁ s₂ e} → Ofes [ A , B ] → Set _
Contractive {A = A}{B} F = ∀ {x y : Ofe.Carrier A}{n} → (► A) [ x ≈⟨ n ⟩ y ] → B [ F ⟨$⟩ x ≈⟨ n ⟩ F ⟨$⟩ y ]

open Later

-- pre-composing a non-expansive function to a contractive function preserves contractivity
.[_∘_]-contractive : ∀ {s₁ s₂ e}{A B C : Ofe s₁ s₂ e}(F : A ⟶ B)(G : B ⟶ C) →
                      Contractive F → Contractive (Ofes [ G ∘ F ])
[_∘_]-contractive F G p eq = cong G (p eq)

.next-co : ∀ {s₁ s₂ e}{A : Ofe s₁ s₂ e} → Contractive (next-ne A)
next-co eq = eq

.next-contractive : ∀ {s₁ s₂ e}{A B : Ofe s₁ s₂ e}{G} →
                    (∃ λ (F : Ofes [ ► A , B ]) → Ofes [ G ≡ Ofes [ F ∘ next-ne A ] ]) → Contractive G
next-contractive {A = A}{B}{G} (F , eq) {x}{y}{n} eq' =
  begin
    G ⟨$⟩ x
  ↓⟨ (NE.limit₁ _ _ G (Ofes [ F ∘ next-ne A ]) eq) n (Ofe.≈ₙ-refl A) ⟩
    Ofes [ F ∘ next-ne A ] ⟨$⟩ x
  ↓⟨ [ (next-ne A) ∘ F ]-contractive next-co eq' ⟩
    Ofes [ F ∘ next-ne A ] ⟨$⟩ y
  ↑⟨ (NE.limit₁ _ _ G (Ofes [ F ∘ next-ne A ]) eq) n (Ofe.≈ₙ-refl A) ⟩
    G ⟨$⟩ y
  ∎
  where open OfeReasoning B

.contractive-next : ∀ {s₁ s₂ e}{A B : Ofe s₁ s₂ e}{G : Ofes [ A , B ]} →
                    Contractive G → (∃ λ (F : Ofes [ ► A , B ]) → Ofes [ G ≡ Ofes [ F ∘ next-ne A ] ])
contractive-next {B = B}{G = G} p =
  record { _⟨$⟩_ = _⟨$⟩_ G ; cong = p } ,
  λ x≈y → NE.≈-cong _ _ G x≈y
