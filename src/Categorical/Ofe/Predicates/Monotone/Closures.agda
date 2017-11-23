open import Categorical.Preorder

module Categorical.Ofe.Predicates.Monotone.Closures {p ℓ} (preorder : PreorderPlus p ℓ ℓ) where

import Relation.Binary.PropositionalEquality as PEq

open import Categories.Category
open import Categories.Functor.Core

open import Categorical.Ofe
open import Categorical.Ofe.Predicates
open import Categorical.Ofe.Predicates.Monotone preorder
open import Categories.Support.EqReasoning

open Ofe
open Category
open Functor

private
  O = Preorder preorder
  module O = Category O
  open Category O using () renaming (Obj to Shape)

module MonotoneClos {o e e'}(P : Pred Shape {o}{e}{e'}) where

  open import Categorical.Ofe.Predicates.Closures

  -- morally: omap x ≔ ∀ x' → x ⇒ x' → P x'
  omap = λ x → ∀[ Obj O ] λ x' → ∀[ O [ x , x' ] ] λ _ → P x'

  hmap : ∀ {A B} → O [ A , B ] → Ofes [ omap A , omap B ]
  _⟨$⟩_ (hmap A⇒B) f X B⇒X = f X (O [ B⇒X ∘ A⇒B ])
  cong (hmap A⇒B) f≡g X B⇒Y = f≡g X (O [ B⇒Y ∘ A⇒B ])

  ∀[_]≤ : Obj MP
  F₀ ∀[_]≤ X = omap X
  F₁ ∀[_]≤ A⇒B = hmap A⇒B
  identity ∀[_]≤ {x = f}{g} f≡g X A⇒X =
    begin
      f X (O [ A⇒X ∘ Category.id O ])
        ↓≣⟨ PEq.cong (f X) (Category.identityʳ O) ⟩
      f X A⇒X
        ↓⟨ f≡g X A⇒X ⟩
      g X A⇒X ∎
    where open SetoidReasoning (setoid (P X))
  homomorphism ∀[_]≤ {f = X⇒Y} {Y⇒Z} {x = f} {g} f≡g X Z⇒X =
    begin
      f X (O [ Z⇒X ∘ O [ Y⇒Z ∘ X⇒Y ] ])
        ↓⟨ f≡g X _ ⟩
      g X (O [ Z⇒X ∘ O [ Y⇒Z ∘ X⇒Y ] ])
        ↑≣⟨ PEq.cong (g X) (Category.assoc O) ⟩
      g X (O [ O [ Z⇒X ∘ Y⇒Z ] ∘ X⇒Y ])
        ↓≣⟨ PEq.refl ⟩
      (Ofes [ hmap Y⇒Z ∘ hmap X⇒Y ] ⟨$⟩ g) X Z⇒X ∎
    where open SetoidReasoning (setoid (P X))
  F-resp-≡ ∀[_]≤ {F = F}{G} F≡G {x = f}{g} f≡g X B⇒A =
    begin
    f X (O [ B⇒A ∘ F ])
      ↓≣⟨ PEq.cong (f X) (Category.∘-resp-≡ O PEq.refl F≡G) ⟩
    f X (O [ B⇒A ∘ G ])
      ↓⟨ f≡g X _ ⟩
    g X (O [ B⇒A ∘ G ]) ∎
    where open SetoidReasoning (setoid (P X))

open MonotoneClos using (∀[_]≤) public
