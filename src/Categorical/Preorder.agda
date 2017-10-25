open import Relation.Binary as Relation renaming (Preorder to PO) using ()
open import Level
import Function

import Relation.Binary.PropositionalEquality as PEq

module Categorical.Preorder where

record PreorderPlus ℓ₁ ℓ₂ ℓ₃ : Set (suc ℓ₁ ⊔ suc ℓ₂ ⊔ suc ℓ₃) where
  field
    po : PO ℓ₁ ℓ₂ ℓ₃

  open PO po renaming (_∼_ to _≤_) public

  field
    assoc : ∀ {c c' c'' c'''}{p : c ≤ c'}{p' : c' ≤ c''}{p'' : c'' ≤ c'''} →
           trans p (trans p' p'') PEq.≡ trans (trans p p') p''
    reflˡ : ∀ {c c'}{p : c ≤ c'} → trans refl p PEq.≡ p
    reflʳ : ∀ {c c'}{p : c ≤ c'} → trans p refl PEq.≡ p

open import Categories.Category

Preorder : ∀ {ℓ₁ ℓ₂ ℓ₃} → PreorderPlus ℓ₁ ℓ₂ ℓ₃ → Category _ _ _
Preorder po = record {
  Obj = Carrier ;
  _⇒_ = _≤_ ;
  _≡_ = PEq._≡_ ;
  id  = refl ;
  _∘_ = Function.flip trans ;
  assoc = assoc ;
  identityʳ = reflˡ ;
  identityˡ = reflʳ ;
  equiv = PEq.isEquivalence ;
  ∘-resp-≡ = λ{ PEq.refl PEq.refl → PEq.refl }}

  where open PreorderPlus po
