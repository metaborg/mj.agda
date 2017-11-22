open import Categories.Support.Equivalence

module Categorical.Ofe.Predicates where

open import Level

open import Data.Product
open import Data.Nat using (ℕ)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary using (IsPreorder) renaming (Preorder to Po)
open import Relation.Binary.PropositionalEquality as PEq using () renaming (_≡_ to _≣_)

open import Categories.Category
open import Categories.Support.EqReasoning
open import Categories.Support.Equivalence

open import Categorical.Ofe

open _⟶_
open Category
open Ofe

module _ {ℓ}(S : Set ℓ){o e e'} where
  module Ofes = Category (Ofes {o}{e}{e'})

  Pred = ∀ (c : S) → Ofe o e e'

  Preds : Category _ _ _
  Obj Preds = Pred
  _⇒_ Preds P Q = ∀ {Σ} → (P Σ) ⟶ (Q Σ)
  _≡_ Preds {P}{Q} f g = ∀ {Σ}(x : Carrier (P Σ)) → (Q Σ) [ (f ⟨$⟩ x) ≈ (g ⟨$⟩ x) ]
  id Preds = Ofes.id
  _∘_ Preds = λ f g {Σ} → Ofes._∘_ f g
  assoc Preds {A}{f = f}{g}{h} x = Ofes.assoc {f = f}{g}{h} (≈-refl (A _))
  identityˡ Preds {A}{B}{f} x = Ofes.identityˡ {f = f} (≈-refl (A _))
  identityʳ Preds {A}{B}{f} x = Ofes.identityʳ {f = f} (≈-refl (A _))
  equiv Preds {A}{B} = record
    { refl  = λ x → ≈-refl (B _)
    ; sym   = λ eq x → ≈-sym (B _) (eq x)
    ; trans = λ eq₁ eq₂ x → ≈-trans (B _) (eq₁ x) (eq₂ x) }
  ∘-resp-≡ Preds {A}{B}{C}{f}{g}{h}{i} f≡g h≡i {Σ} x =
    begin
      f ⟨$⟩ (h ⟨$⟩ x)
    ↓⟨ NE.≈-cong _ _ f (h≡i x) ⟩
      f ⟨$⟩ (i ⟨$⟩ x)
    ↓⟨ f≡g (i ⟨$⟩ x) ⟩
      g ⟨$⟩ (i ⟨$⟩ x)
    ∎
    where open SetoidReasoning (setoid (C Σ))

module _ {ℓ}{S : Set ℓ}{o e e'}(P : Pred S {o}{e}{e'}) where
  -- lift the Ofe equality into their heterogeneous counterparts
  data _[_≅_] {c} : ∀ {c'} → Carrier (P c) → Carrier (P c') → Set (e ⊔ e') where
    hrefl : ∀ {l r} → (P c) [ l ≈ r ] → _[_≅_] l r

  .≅-equiv : ∀ {c} → IsEquivalence (λ (x y : Carrier (P c)) → _[_≅_] x y)
  ≅-equiv = record
    { refl = λ {x} → hrefl (Ofe.≈-refl (P _))
    ; sym = λ { {i} {j} (hrefl p) → hrefl (Ofe.≈-sym (P _) p) }
    ; trans = λ { (hrefl p) (hrefl q) → hrefl (Ofe.≈-trans (P _) p q) }
    }

  data _[_≅⟨_⟩_] {c} : ∀ {c'} → Carrier (P c) → ℕ → Carrier (P c') → Set (e ⊔ e') where
    hrefl : ∀ {l r n} → (P c) [ l ≈⟨ n ⟩ r ] → _[_≅⟨_⟩_] l n r

  .≅⟨⟩-equiv : ∀ {n c} → IsEquivalence (λ (x y : Carrier (P c)) → _[_≅⟨_⟩_] x n y)
  ≅⟨⟩-equiv = record
    { refl = λ {x} → hrefl (Ofe.≈ₙ-refl (P _))
    ; sym = λ { {i} {j} (hrefl p) → hrefl (Ofe.≈ₙ-sym (P _) p) }
    ; trans = λ { (hrefl p) (hrefl q) → hrefl (Ofe.≈ₙ-trans (P _) p q) }
    }

.≅-cong : ∀ {ℓ o e e'}{S : Set ℓ}{I J : Pred S {o}{e}{e'}}
          {l l'}{r : Carrier (I l)}{r' : Carrier (I l')} →
          (f : Preds S [ I , J ]) → I [ r ≅ r' ] → J [ (f ⟨$⟩ r) ≅ (f ⟨$⟩ r') ]
≅-cong f (hrefl x) = (hrefl (NE.≈-cong _ _ f x))
