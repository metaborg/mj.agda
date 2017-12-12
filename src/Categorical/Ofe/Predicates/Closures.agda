module Categorical.Ofe.Predicates.Closures where

open import Level

open import Data.Product
open import Data.Nat using (ℕ)
open import Relation.Binary using (IsPreorder) renaming (Preorder to Po)
open import Relation.Binary.PropositionalEquality as PEq using () renaming (_≡_ to _≣_)

open import Categories.Category
open import Categories.Support.EqReasoning
open import Categories.Functor.Core

open import Categorical.Preorder
open import Categorical.Ofe
open import Categorical.Ofe.Predicates

open Category
open Ofe

module _ {ℓ o e e'}(A : Set ℓ)(B : Pred A {o}{e}{e'}) where
  module B a = Ofe (B a)

  private
    Pack : Set _
    Pack = ∃ λ (a : A) → B.Carrier a

    unpackₙ : ∀ {a}{x y : B.Carrier a}{n} → B [ x ≅⟨ n ⟩ y ] → (B a) [ x ≈⟨ n ⟩ y ]
    unpackₙ (hrefl eq) = eq

  ∃[_] : Ofe _ _ _
  setoid ∃[_] = record
    { Carrier = Pack
    ; _≈_ = λ p q → B [ proj₂ p ≅ proj₂ q ]
    ; isEquivalence = record
      { refl = λ {x} → hrefl (Ofe.≈-refl (B (proj₁ x)))
      ; sym = λ { {i} {j} (hrefl p) → hrefl (Ofe.≈-sym (B (proj₁ j)) p) }
      ; trans = λ { (hrefl p) (hrefl q) → hrefl (Ofe.≈-trans (B _) p q) }
      }
    }
  _≈⟨_⟩_ ∃[_] x n y = B [ proj₂ x ≅⟨ n ⟩ proj₂ y ]
  equiv  ∃[_] = record
    { refl = hrefl (≈ₙ-refl (B _))
    ; sym = λ{ (hrefl eq) → hrefl (≈ₙ-sym (B _) eq) }
    ; trans = λ{ (hrefl eq) (hrefl eq') → hrefl (≈ₙ-trans (B _) eq eq') } }
  limit₁ ∃[_] (hrefl eq) n = hrefl (limit₁ (B _) eq n)
  limit₂ ∃[_] {x = x} eq with eq 0
  ... | hrefl _ = hrefl (limit₂ (B _) λ n → unpackₙ (eq n))
  monotone ∃[_] n≤m (hrefl eqₙ) = hrefl (monotone (B _) n≤m eqₙ)

  ∀[_] : Ofe _ _ _
  setoid ∀[_] = record
    { Carrier = ∀ (a : A) → B.Carrier a
    ; _≈_ = λ p q → ∀ (a : A) → (B a) [ p a ≈ q a ]
    ; isEquivalence = record
      { refl = λ a → ≈-refl (B _)
      ; sym = λ { p a → ≈-sym (B _) (p a) }
      ; trans = λ { p q a → ≈-trans (B _) (p a) (q a) }
      }
    }
  _≈⟨_⟩_ ∀[_] x n y = ∀ (a : A) → (B a) [ x a ≈⟨ n ⟩ y a ]
  equiv  ∀[_] = record
    { refl = λ a → ≈ₙ-refl (B a)
    ; sym = λ x a → ≈ₙ-sym (B a) (x a)
    ; trans = λ x y a → ≈ₙ-trans (B a) (x a) (y a) }
  limit₁ ∀[_] p n = λ a → limit₁ (B a) (p a) n
  limit₂ ∀[_] {x = x} eq = λ a → limit₂ (B a) λ n → eq n a
  monotone ∀[_] = λ n≤m eq a → monotone (B a) n≤m (eq a)

module _ {ℓ o e e'}(A : Set ℓ)(B : CPred A {o}{e}{e'}) where
  open import Categorical.Ofe.Cofe
  open Cofe
  ∀[_]-cofe : Cofe _ _ _
  ofe ∀[_]-cofe = ∀[ A ] λ a → ofe (B a)
  conv ∀[_]-cofe ch =
    lim
      (λ a → at-∞ (conv (B a) (ch' a)))
      (λ n a → limit (conv (B a) (ch' a)) n)
    where
      ch' : ∀ (a : A) → Chain (ofe (B a))
      ch' a = chain-map (record { _⟨$⟩_ = λ x → x a ; cong = λ xeq → xeq a }) ch

module MonotoneClos
  {o ℓ ℓ'}(po : PreorderPlus o ℓ ℓ')
  {o e e'}(P : Pred (PreorderPlus.Carrier po){o}{e}{e'}) where

  open PreorderPlus po

  open Category Ord using () renaming (Obj to Shape)
  open import Categorical.Ofe.Predicates.Monotone po
  open Functor

  -- morally: omap x ≔ ∀ x' → x ⇒ x' → P x'
  omap = λ x → ∀[ Shape ] λ x' → ∀[ Ord [ x , x' ] ] λ _ → P x'

  hmap : ∀ {A B} → Ord [ A , B ] → Ofes [ omap A , omap B ]
  _⟨$⟩_ (hmap A⇒B) f X B⇒X = f X (Ord [ B⇒X ∘ A⇒B ])
  cong (hmap A⇒B) f≡g X B⇒Y = f≡g X (Ord [ B⇒Y ∘ A⇒B ])

  ∀[_]≤ : Obj MP
  F₀ ∀[_]≤ X = omap X
  F₁ ∀[_]≤ A⇒B = hmap A⇒B
  identity ∀[_]≤ {x = f}{g} f≡g X A⇒X =
    begin
      f X (Ord [ A⇒X ∘ Category.id Ord ])
        ↓≣⟨ PEq.cong (f X) (Category.identityʳ Ord) ⟩
      f X A⇒X
        ↓⟨ f≡g X A⇒X ⟩
      g X A⇒X ∎
    where open OfeReasoning (P X)
  homomorphism ∀[_]≤ {f = X⇒Y} {Y⇒Z} {x = f} {g} f≡g X Z⇒X =
    begin
      f X (Ord [ Z⇒X ∘ Ord [ Y⇒Z ∘ X⇒Y ] ])
        ↓⟨ f≡g X _ ⟩
      g X (Ord [ Z⇒X ∘ Ord [ Y⇒Z ∘ X⇒Y ] ])
        ↑≣⟨ PEq.cong (g X) (Category.assoc Ord) ⟩
      g X (Ord [ Ord [ Z⇒X ∘ Y⇒Z ] ∘ X⇒Y ])
        ↓≣⟨ PEq.refl ⟩
      (Ofes [ hmap Y⇒Z ∘ hmap X⇒Y ] ⟨$⟩ g) X Z⇒X ∎
    where open OfeReasoning (P X)
  F-resp-≡ ∀[_]≤ {F = F}{G} F≡G {x = f}{g} f≡g X B⇒A =
    begin
    f X (Ord [ B⇒A ∘ F ])
      ↓≣⟨ PEq.cong (f X) (Category.∘-resp-≡ Ord PEq.refl F≡G) ⟩
    f X (Ord [ B⇒A ∘ G ])
      ↓⟨ f≡g X _ ⟩
    g X (Ord [ B⇒A ∘ G ]) ∎
    where open OfeReasoning (P X)

open MonotoneClos using (∀[_]≤) public

{- TODO are all of the above functors?

∃Functor : ∀ {o e e' ℓ}(A : Set ℓ) → Functor (Preds A {o}{e}{e'}) Ofes
F₀ (∃Functor A) = ∃[ A ]
F₁ (∃Functor A) = {!!}
identity (∃Functor A) = {!!}
homomorphism (∃Functor A) = {!!}
F-resp-≡ (∃Functor A) = {!!}
-}
