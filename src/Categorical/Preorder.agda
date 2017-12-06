open import Relation.Binary as Relation renaming (Preorder to PO) using ()
open import Relation.Binary.Core using (IsEquivalence)
open import Level
import Function

import Relation.Binary.PropositionalEquality as PEq
open import Categories.Support.Equivalence

module Categorical.Preorder where

record PreorderPlus ℓ₁ ℓ₂ ℓ₃ : Set (suc ℓ₁ ⊔ suc ℓ₂ ⊔ suc ℓ₃) where
  field
    preorder : PO ℓ₁ ℓ₂ ℓ₃

  open PO preorder renaming (_∼_ to _≤_) public

  field
    unique : ∀ {c c'}(p q : c ≤ c') → p PEq.≡ q

  _≥_ = Function.flip _≤_

  op : PreorderPlus _ _ _
  op = record {
    preorder = record
      { Carrier = Carrier
      ; _≈_ = _≈_
      ; _∼_ = λ a b → b ≤ a
      ; isPreorder = record
        { isEquivalence = isEquivalence
        ; reflexive = λ x → reflexive (IsEquivalence.sym isEquivalence x)
        ; trans = λ p q → trans q p } }
        ; unique = unique }

  open import Categories.Category

  Ord : Category _ _ _
  Ord = record {
    Obj = Carrier ;
    _⇒_ = _≤_ ;
    _≡_ = PEq._≡_ ;
    id  = refl ;
    _∘_ = Function.flip trans ;
    assoc = unique _ _;
    identityʳ = unique _ _;
    identityˡ = unique _ _;
    equiv = PEq.isEquivalence ;
    ∘-resp-≡ = λ{ PEq.refl PEq.refl → PEq.refl }}
