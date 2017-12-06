module Categorical.Thin where


open import Relation.Binary.PropositionalEquality using (cong) renaming (_≡_ to _≣_; isEquivalence to ≣-equiv; refl to ≣-refl)
open import Relation.Binary as Relation renaming (Preorder to PO) using ()
open import Level renaming (suc to lsuc)
import Function

open import Categories.Category
open Category

record Thin {c ℓ e} : Set (lsuc e ⊔ lsuc ℓ ⊔ lsuc c) where
  field
    Ord : Category c ℓ e
    ⇒-unique : ∀ {X Y}(F G : Ord [ X , Y ]) → Ord [ F ≡ G ]

open Thin

Preorder : ∀ {ℓ₁ ℓ₂ ℓ₃} → (po : PO ℓ₁ ℓ₂ ℓ₃) → (unique : ∀ {x y} → (p q : PO._∼_ po x y) → p ≣ q) → Thin
Ord (Preorder po unique) = record {
  Obj = Carrier ;
  _⇒_ = _≤_ ;
  _≡_ = _≣_ ;
  id  = refl ;
  _∘_ = Function.flip trans ;
  assoc = unique _ _;
  identityʳ = unique _ _ ;
  identityˡ = unique _ _ ;
  equiv = ≣-equiv ;
  ∘-resp-≡ = λ{ ≣-refl ≣-refl → ≣-refl }}
  where open PO po renaming (_∼_ to _≤_)
⇒-unique (Preorder po unique) = unique

open import Data.Nat
open import Data.Nat.Properties using (≤-preorder)

ℕ≤ : Thin
ℕ≤ = Preorder ≤-preorder thin
  where
    thin : ∀ {x y}(p q : x ≤ y) → p ≣ q
    thin z≤n z≤n = ≣-refl
    thin (s≤s p) (s≤s q) = cong s≤s (thin p q)
