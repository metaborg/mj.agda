module Categorical.Ofe.Predicates.Closures where

open import Level

open import Data.Product
open import Data.Nat using (ℕ)
open import Relation.Binary using (IsPreorder) renaming (Preorder to Po)
open import Relation.Binary.PropositionalEquality as PEq using () renaming (_≡_ to _≣_)

open import Categories.Category
open import Categories.Support.EqReasoning

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
