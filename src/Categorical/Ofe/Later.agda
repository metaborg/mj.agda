module Categorical.Ofe.Later where

open import Relation.Binary.PropositionalEquality using () renaming (refl to ≣-refl)
open import Categories.Support.Equivalence using (Setoid)
open import Categories.Support.EqReasoning
open import Relation.Binary using (IsEquivalence)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Level

open import Categories.Category
open import Categories.Functor.Core

open import Categorical.Ofe
open import Categorical.Ofe.Products

open Functor
open Category

module Later {s₁ s₂ e}(o : Ofe s₁ s₂ e) where
  open Ofe o

  data Later : Set s₁ where
    next  : ∀ (x : Carrier) → Later

  unnext : Later → Carrier
  unnext (next x) = x

  data _later≈_ : Later → Later → Set s₂ where
    next : ∀ {x y} → x ≈ y → next x later≈ next y

  .next∘unnext : ∀ {x} → next (unnext x) later≈ x
  next∘unnext {next x} = next ≈-refl

  module _ where
    open Setoid
    later-setoid : Setoid _ _
    Carrier later-setoid = Later
    _≈_ later-setoid = _later≈_
    isEquivalence later-setoid = record
      { refl = λ where
          {next x} → next ≈-refl
      ; sym = λ where
          (next eq) → next (≈-sym eq)
      ; trans = λ where
          (next p) (next q) → next (≈-trans p q) }

  data _later≈⟨_⟩_ : Later → Fuel → Later → Set e where
    now   : ∀ {x y} → x later≈⟨ ℕ.zero ⟩ y
    next  : ∀ {x y n} → x ≈⟨ n ⟩ y → (next x) later≈⟨ ℕ.suc n ⟩ (next y)

  unnext-eq : ∀ {x y n} → x later≈⟨ ℕ.suc n ⟩ y → unnext x ≈⟨ n ⟩ unnext y
  unnext-eq (next eq) = eq

-- it is a functor in the category of Ofes
module LaterOfe {s₁ s₂ e} where
  omap : (T : Ofe s₁ s₂ e) → Ofe _ _ _
  omap T = record
    { setoid = later-setoid
    ; _≈⟨_⟩_ = _later≈⟨_⟩_
    ; equiv = λ {n} → ≈ₙequiv {n}
    ; limit₁ = limit₁'
    ; limit₂ = limit₂'
    ; monotone = mono
    }
    where
      module T = Ofe T
      open Later T

      .limit₁' : ∀ {x y} → x later≈ y → (n : ℕ) → x later≈⟨ n ⟩ y
      limit₁' x ℕ.zero = now
      limit₁' (next x) (ℕ.suc n) = next (T.limit₁ x n)

      open IsEquivalence
      .≈ₙequiv : ∀ {n} → IsEquivalence (λ x y → x later≈⟨ n ⟩ y)
      refl (≈ₙequiv {n}) {next x} = limit₁' (next T.≈-refl) n
      sym ≈ₙequiv now = now
      sym ≈ₙequiv (next x≈ₙy) = next (Ofe.≈ₙ-sym T x≈ₙy)
      trans ≈ₙequiv now now = now
      trans ≈ₙequiv (next x≈ₙy) (next y≈ₙz) = next (Ofe.≈ₙ-trans T x≈ₙy y≈ₙz)

      .limit₂' : ∀ {x y} → ((n : ℕ) → x later≈⟨ n ⟩ y) → (x later≈ y)
      limit₂' {next x} {next y} x≋y = next (T.limit₂ λ n → unnext-eq (x≋y (ℕ.suc n)))

      .mono : ∀ {n n' : ℕ} {x y} → n' ≤ n → x later≈⟨ n ⟩ y → x later≈⟨ n' ⟩ y
      mono z≤n x≈ₙy = now
      mono (s≤s le) (next x≈ₙy) = next (T.monotone le x≈ₙy)

  open Later public

  next-ne : ∀ (A : Obj Ofes) → Ofes [ A , omap A ]
  _⟨$⟩_ (next-ne _) x = next x
  cong (next-ne _) {ℕ.zero} {x} {y} eq = now
  cong (next-ne A) {ℕ.suc n} {x} {y} eq = next (Ofe.monotone A (n≤1+n n) eq)
    where open import Data.Nat.Properties

  hmap : ∀ {A B} → Ofes [ A , B ] → Ofes [ omap A , omap B ]
  hmap {A = A}{B} f = record
    { _⟨$⟩_ = λ x → next (f ⟨$⟩ (unnext _ x))
    ; cong  = λ{ now → now ; (next eq) → next (cong f eq) }}

  .homomorph : ∀ {X Y Z}{f : Ofes [ X , Y ]}{g : Ofes [ Y , Z ]} →
               Ofes [ hmap (Ofes [ g ∘ f ]) ≡ Ofes [ hmap g ∘ hmap f ] ]
  homomorph {X = X} {Y} {Z} {f} {g} {_} {x} {y} x≈y =
    begin
      hmap (Ofes [ g ∘ f ]) ⟨$⟩ x
    ↓⟨ cong (hmap (Ofes [ g ∘ f ])) x≈y ⟩
      hmap (Ofes [ g ∘ f ]) ⟨$⟩ y
    ↓≣⟨ ≣-refl ⟩
      Ofes [ hmap g ∘ hmap f ] ⟨$⟩ y
    ∎
    where open OfeReasoning (omap Z)

  .identity′ : ∀ {A} → Ofes [ hmap {A = A} (Category.id Ofes) ≡ Category.id Ofes ]
  identity′ {A} {x = next x}{next y} x≈y = x≈y

  .resp : ∀ {A B}{F G : Ofes [ A , B ]} → Ofes [ F ≡ G ] → Ofes [ hmap F ≡ hmap G ]
  resp {A}{B}{F}{G} F≡G {x = next x}{y} x≈y =
    begin
      next (F ⟨$⟩ x)
    ↓⟨ cong (next-ne B) (F≡G (Ofe.≈ₙ-refl A)) ⟩
      next (G ⟨$⟩ x)
    ↓⟨ cong (hmap G) x≈y ⟩
      hmap G ⟨$⟩ y
    ∎
    where open OfeReasoning (omap B)

  functor : Endofunctor Ofes
  F₀ functor = omap
  F₁ functor = hmap
  homomorphism functor {f = f}{g} x = homomorph {f = f}{g} x
  identity functor {A} = identity′ {A}
  F-resp-≡ functor {F = F}{G} = resp {F = F}{G}

open LaterOfe using (next; next-ne) renaming (functor to ►F; omap to ►) public

Contractive : ∀ {s₁ s₂ e}{A B : Ofe s₁ s₂ e} → Ofes [ A , B ] → Set _
Contractive {A = A}{B} F = ∀ {x y : Ofe.Carrier A}{n} → (► A) [ next x ≈⟨ n ⟩ next y ] → B [ F ⟨$⟩ x ≈⟨ n ⟩ F ⟨$⟩ y ]

open Later

-- pre-composing a non-expansive function to a contractive function preserves contractivity
.[_∘_]-contractive : ∀ {s₁ s₂ e}{A B C : Ofe s₁ s₂ e}(G : B ⟶ C)(F : A ⟶ B) →
                      Contractive F → Contractive (Ofes [ G ∘ F ])
[_∘_]-contractive G F p eq = cong G (p eq)

.next-co : ∀ {s₁ s₂ e}{A : Ofe s₁ s₂ e} → Contractive (next-ne A)
next-co eq = eq

.next-contractive : ∀ {s₁ s₂ e}{A B : Ofe s₁ s₂ e}{G} →
                    (∃ λ (F : Ofes [ ► A , B ]) → Ofes [ G ≡ Ofes [ F ∘ next-ne A ] ]) → Contractive G
next-contractive {A = A}{B}{G} (F , eq) {x}{y}{n} eq' =
  begin
    G ⟨$⟩ x
  ↓⟨ eq (Ofe.≈ₙ-refl A) ⟩
    Ofes [ F ∘ next-ne A ] ⟨$⟩ x
  ↓⟨ [ F ∘ (next-ne A) ]-contractive next-co eq' ⟩
    Ofes [ F ∘ next-ne A ] ⟨$⟩ y
  ↑⟨ eq (Ofe.≈ₙ-refl A) ⟩
    G ⟨$⟩ y
  ∎
  where open OfeReasoning B

.contractive-next : ∀ {s₁ s₂ e}{A B : Ofe s₁ s₂ e}{G : Ofes [ A , B ]} →
                    Contractive G → (∃ λ (F : Ofes [ ► A , B ]) → Ofes [ G ≡ Ofes [ F ∘ next-ne A ] ])
contractive-next {B = B}{G = G} p =
  record
    { _⟨$⟩_ = λ x → G ⟨$⟩ (unnext _ x)
    ; cong  = λ where {x = next x}{y = next y} eq → p eq
    } , λ x≈y → cong G x≈y

private
  n-iter : ∀ {ℓ}{A : Set ℓ} → ℕ → (f : A → A) → A → A
  n-iter ℕ.zero f x = x
  n-iter (ℕ.suc n) f x = f (n-iter n f x)

-- iterating a contractive function gives a cauchy chain
iterate : ∀ {s₁ s₂ e}{A : Ofe s₁ s₂ e} → (F : Ofes [ A , A ]) →
          .(Contractive F) → Ofe.Carrier A → Chain A
_at_ (iterate F p x) n = n-iter (ℕ.suc n) (_⟨$⟩_ F) x
cauchy (iterate {A = A} F p x) {n = ℕ.zero} z≤n z≤n = p Later.now
cauchy (iterate {A = A} F p x) {n = ℕ.suc n} (s≤s n≤i) (s≤s n≤j) =
  p (Later.next (cauchy (iterate {A = A} F p x) n≤i n≤j))

-- iterating equal functions builds pointwise equal chains
.iterate-cong : ∀ {s₁ s₂ e}{A : Ofe s₁ s₂ e}(F G : Ofes [ A , A ]) (p : Contractive F)(q : Contractive G) →
                Ofes [ F ≡ G ] → ∀ {x y n} → A [ x ≈⟨ n ⟩ y ] →
                (iterate F p x) chain≈⟨ n ⟩ (iterate G q y)
iterate-cong F G p q F≡G {n = n} x≈y ℕ.zero = F≡G x≈y
iterate-cong {A = A} F G p q F≡G {x = x}{y}{n} x≈y (ℕ.suc i) =
  begin
    F ⟨$⟩ (F ⟨$⟩ n-iter i (_⟨$⟩_ F) x)
  ↓⟨ F≡G (Ofe.≈ₙ-refl A) ⟩
    G ⟨$⟩ (F ⟨$⟩ n-iter i (_⟨$⟩_ F) x)
  ↓⟨ cong G (iterate-cong {A = A} F G p q F≡G x≈y i) ⟩
    G ⟨$⟩ (G ⟨$⟩ n-iter i (_⟨$⟩_ G) y)
  ∎
  where open OfeReasoning A

open import Categorical.Ofe.Cofe

►-complete : ∀ {s₁ s₂ e} → Cofe s₁ s₂ e → Cofe _ _ _
►-complete T = record
  { ofe = ► (Cofe.ofe T)
  ; conv = conv' }
  where
    open Cofe T

    unnext-chain : ∀ (c : Chain (► ofe)) → Chain ofe
    _at_   (unnext-chain c) n = unnext _ (c at (ℕ.suc n))
    cauchy (unnext-chain c) {i = i}{j} n≤i n≤j = Later.unnext-eq ofe (cauchy c (s≤s n≤i) (s≤s n≤j))

    conv' : (c : Chain (► ofe)) → Limit c
    at-∞  (conv' c) = next (at-∞ (Cofe.conv T (unnext-chain c)))
    limit (conv' c) n =
      begin
        (c at n)
      ↓⟨ cauchy c (≤-reflexive ≣-refl) (n≤1+n n) ⟩
        (c at ℕ.suc n)
      ↑⟨ Ofe.limit₁ (► ofe) (next∘unnext _) n ⟩
        next (unnext _ (c at ℕ.suc n))
      ↑≣⟨ ≣-refl ⟩
        next (unnext-chain c at n)
      ↓⟨ cong (next-ne _) (limit (conv (unnext-chain c)) n) ⟩
        next (at-∞ (conv (unnext-chain c)))
      ∎
      where open OfeReasoning (► ofe)

open import Categories.Category
open Cofe

-- we can build a fixed point from a contractive function
μ' : ∀ {s₁ s₂ e}(A : Cofe s₁ s₂ e) →
     (F : Ofes [ ofe A , ofe A ]) → .(Contractive F) → Carrier A → Ofes [ ⊤ , ofe A ]
_⟨$⟩_ (μ' A F p a) _ = at-∞ (Cofe.conv A (iterate F p a))
cong  (μ' A F p a) {n = n}{x = x}{y} x≈y =
  cong-conv A
    (iterate F p a)
    (iterate F p a)
    (iterate-cong F F p p (cong F) (≈ₙ-refl A))

-- Because we can build contractive functions from non-expansive functions from ◀ A to A,
-- we can define a μ that is easier to work with.
μ : ∀ {s₁ s₂ e}(A : Cofe s₁ s₂ e) → (F : Ofes [ ► (ofe A) , ofe A ]) → Carrier A → Ofes [ ⊤ , ofe A ]
μ A F = μ' A (Ofes [ F ∘ next-ne (Cofe.ofe A) ]) ([ F ∘ next-ne (Cofe.ofe A) ]-contractive next-co)
