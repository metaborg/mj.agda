open import Level

module Categorical.Ofe.Coproducts {ℓ}{e}{e'} where

open import Data.Nat hiding (_+_; _⊔_)
open import Relation.Binary using (IsEquivalence)
import Relation.Binary.PropositionalEquality as PEq
import Data.Unit as Unit
import Function as Fun

open import Categories.Category
open import Categories.Support.Equivalence

open import Categorical.Ofe
open import Categorical.Ofe.Cofe hiding (_⇨_)

open import Categories.Object.Coproduct (Ofes {ℓ}{e}{e'})

open Category using (Obj)
open Ofe

open import Data.Sum using (_⊎_; inj₁; inj₂) public

module Sum+ {ℓ}{ℓ'} (A B : Setoid ℓ ℓ') where
  module A = Setoid A
  module B = Setoid B

  infixl 4 _⊎≈_
  data _⊎≈_ : (l r : A.Carrier ⊎ B.Carrier) → Set ℓ' where
    inj₁ : ∀ {x y} → x A.≈ y → inj₁ x ⊎≈ inj₁ y
    inj₂ : ∀ {x y} → x B.≈ y → inj₂ x ⊎≈ inj₂ y

  .⊎≈-equiv : IsEquivalence _⊎≈_
  ⊎≈-equiv = record
    { refl = λ where
      {inj₁ x} → inj₁ A.refl
      {inj₂ y} → inj₂ B.refl
    ; sym = λ where
      (inj₁ p) → inj₁ (A.sym p)
      (inj₂ p) → inj₂ (B.sym p)
    ; trans = λ where
      (inj₁ p) (inj₁ q) → inj₁ (A.trans p q)
      (inj₂ p) (inj₂ q) → inj₂ (B.trans p q) }

  open Setoid
  ⊎-setoid : Setoid ℓ ℓ'
  Carrier ⊎-setoid = A.Carrier ⊎ B.Carrier
  _≈_ ⊎-setoid = _⊎≈_
  isEquivalence ⊎-setoid = ⊎≈-equiv

private
  module Binary (A B : Ofe ℓ e e') where

    module A = Ofe A
    module B = Ofe B

    oid = Sum+.⊎-setoid A.setoid B.setoid
    open Sum+
    open Setoid oid renaming (Carrier to C; _≈_ to _C≈_)

    data _⊎≈⟨_⟩_ : C → ℕ → C → Set e' where
      inj₁ : ∀ {x n y} → x A.≈⟨ n ⟩ y → inj₁ x ⊎≈⟨ n ⟩ inj₁ y
      inj₂ : ∀ {x n y} → x B.≈⟨ n ⟩ y → inj₂ x ⊎≈⟨ n ⟩ inj₂ y

    unpack₁ : ∀ {x n y} → inj₁ x ⊎≈⟨ n ⟩ inj₁ y → x A.≈⟨ n ⟩ y
    unpack₁ (inj₁ p) = p

    unpack₂ : ∀ {x n y} → inj₂ x ⊎≈⟨ n ⟩ inj₂ y → x B.≈⟨ n ⟩ y
    unpack₂ (inj₂ p) = p

    .⊎≈ₙ-equiv : ∀ {n} → IsEquivalence (λ x y → _⊎≈⟨_⟩_ x n y)
    ⊎≈ₙ-equiv = record
      { refl = λ where
        {inj₁ x} → inj₁ A.≈ₙ-refl
        {inj₂ y} → inj₂ B.≈ₙ-refl
      ; sym = λ where
        (inj₁ p) → inj₁ (A.≈ₙ-sym p)
        (inj₂ p) → inj₂ (B.≈ₙ-sym p)
      ; trans = λ where
        (inj₁ p) (inj₁ q) → inj₁ (A.≈ₙ-trans p q)
        (inj₂ p) (inj₂ q) → inj₂ (B.≈ₙ-trans p q) }

    .lim₁ : ∀ {x y} → x C≈ y → (n : ℕ) → x ⊎≈⟨ n ⟩ y
    lim₁ (inj₁ eq) n = inj₁ (A.limit₁ eq n)
    lim₁ (inj₂ eq) n = inj₂ (B.limit₁ eq n)

    .lim₂ : ∀ {x y} → ((n : ℕ) → x ⊎≈⟨ n ⟩ y) → x C≈ y
    lim₂ {inj₁ x} {inj₁ y} eq = inj₁ (A.limit₂ λ n → unpack₁ (eq n))
    lim₂ {inj₁ x} {inj₂ y} eq with eq 0
    ... | ()
    lim₂ {inj₂ x} {inj₁ y} eq with eq 0
    ... | ()
    lim₂ {inj₂ x} {inj₂ y} eq = inj₂ (B.limit₂ λ n → unpack₂ (eq n))

    .mono : ∀ {n x y m} → m ≤ n → x ⊎≈⟨ n ⟩ y → x ⊎≈⟨ m ⟩ y
    mono p (inj₁ x) = inj₁ (monotone A p x)
    mono p (inj₂ x) = inj₂ (monotone B p x)

    ⊕ : Ofe ℓ e e'
    setoid ⊕ = oid
    _≈⟨_⟩_ ⊕ = _⊎≈⟨_⟩_
    equiv  ⊕ = ⊎≈ₙ-equiv
    limit₁ ⊕ = lim₁
    limit₂ ⊕ = lim₂
    monotone ⊕ = mono

open Binary using (_⊎≈⟨_⟩_; inj₁; inj₂) public

module _ where
  open BinCoproducts
  binary : BinCoproducts
  _+_ binary A B = Binary.⊕ A B
  i₁ binary = record
    { _⟨$⟩_ = inj₁
    ; cong = Binary.inj₁ }
  i₂ binary = record
    { _⟨$⟩_ = inj₂
    ; cong = Binary.inj₂ }
  [_,_] binary = λ f g → record
    { _⟨$⟩_ = λ where
      (inj₁ x) → f ⟨$⟩ x
      (inj₂ y) → g ⟨$⟩ y
    ; cong = λ where
      (Binary.inj₁ x) → cong f x
      (Binary.inj₂ x) → cong g x }
  commute₁ binary {f = f} eq = cong f eq
  commute₂ binary {g = g} eq = cong g eq
  universal binary {A} {B} {C} eq _ (Binary.inj₁ x≈y) = ≈ₙ-sym C (eq (≈ₙ-sym A x≈y))
  universal binary {A} {B} {C} _ eq (Binary.inj₂ x≈y) = ≈ₙ-sym C (eq (≈ₙ-sym B x≈y))
