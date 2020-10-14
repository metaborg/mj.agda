module Data.List.Prefix where

open import Level
open import Data.Nat
open import Data.List
open import Data.List.At
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any hiding (map)
open import Data.List.Relation.Binary.Pointwise as P hiding (refl; map)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as ≡

-- prefix predicate for lists
infix 4 _⊑_
data _⊑_ {a} {A : Set a} : List A → List A → Set a where
  [] : ∀ {ys} → [] ⊑ ys
  _∷_ : ∀ x {xs ys} → xs ⊑ ys → x ∷ xs ⊑ x ∷ ys

⊑-refl : ∀ {a} {A : Set a} → Reflexive (_⊑_ {A = A})
⊑-refl {x = []} = []
⊑-refl {x = x ∷ xs} = x ∷ ⊑-refl

⊑-trans : ∀ {a} {A : Set a} → Transitive (_⊑_ {A = A})
⊑-trans [] _ = []
⊑-trans (x ∷ p) (.x ∷ q) = x ∷ ⊑-trans p q

open import Relation.Binary.PropositionalEquality

⊑-unique : ∀ {a}{A : Set a}{k l : List A}(xs ys : k ⊑ l) → xs ≡ ys
⊑-unique [] [] = refl
⊑-unique (x ∷ xs) (.x ∷ ys) = cong (λ u → x ∷ u) (⊑-unique xs ys)

⊑-trans-refl : ∀ {a}{A : Set a}{k l}{xs : k ⊑ l} → ⊑-trans {A = A} ⊑-refl xs ≡ xs
⊑-trans-refl {xs = []} = refl
⊑-trans-refl {xs = x ∷ xs} = cong (λ u → x ∷ u) ⊑-trans-refl

⊑-trans-refl' : ∀ {a}{A : Set a}{k l}{xs : k ⊑ l} → ⊑-trans {A = A} xs ⊑-refl ≡ xs
⊑-trans-refl' {xs = []} = refl
⊑-trans-refl' {xs = x ∷ xs} = cong (λ u → x ∷ u) ⊑-trans-refl'

⊑-trans-assoc : ∀ {a}{A : Set a}{k l m n : List A}{p : k ⊑ l}{q : l ⊑ m}{r : m ⊑ n} →
                ⊑-trans p (⊑-trans q r) ≡ ⊑-trans (⊑-trans p q) r
⊑-trans-assoc {p = []} {q} = refl
⊑-trans-assoc {p = x ∷ p} {.x ∷ q} {.x ∷ r} = cong (λ u → x ∷ u) ⊑-trans-assoc

remainder : ∀ {a}{A : Set a}{xs ys : List A} → xs ⊑ ys → List A
remainder ([] {ys}) = ys
remainder (x ∷ xs) = remainder xs

-- list extensions; reverse prefix relation
infix 4 _⊒_
_⊒_ : ∀ {a} {A : Set a} → List A → List A → Set a
xs ⊒ ys = ys ⊑ xs

-- appending to a list gives a list extension;
-- or, appending to a list makes the original a prefix
∷ʳ-⊒ : ∀ {a} {A : Set a} (x : A) xs → xs ∷ʳ x ⊒ xs
∷ʳ-⊒ x [] = []
∷ʳ-⊒ x (x₁ ∷ Σ₁) = x₁ ∷ (∷ʳ-⊒ x Σ₁)

-- indexes into a prefix point to the same element in extensions
xs⊒ys[i] : ∀ {a} {A : Set a} {xs : List A} {ys : List A} {i y} →
           xs [ i ]= y → (p : ys ⊒ xs) → ys [ i ]= y
xs⊒ys[i] () []
xs⊒ys[i] {i = zero} p (x ∷ a) = p
xs⊒ys[i] {i = suc i} p (x ∷ a) = xs⊒ys[i] p a

-- prefix is preserved by map
⊑-map : ∀ {a b} {A : Set a} {B : Set b} {xs ys : List A} {f : A → B} →
        xs ⊑ ys → map f xs ⊑ map f ys
⊑-map [] = []
⊑-map {f = f} (x ∷ p) = f x ∷ (⊑-map p)

-- all elemens in a list, also exist in it's extensions
∈-⊒ : ∀ {a}{A : Set a}{xs : List A}{x} → x ∈ xs → ∀ {ys} → ys ⊒ xs → x ∈ ys
∈-⊒ () []
∈-⊒ (here px) (x ∷ q) = here px
∈-⊒ (there p) (x ∷ q) = there (∈-⊒ p q)

∈-⊒-refl : ∀ {a}{A : Set a}{xs : List A}{x}{p : x ∈ xs} → ∈-⊒ p ⊑-refl ≡ p
∈-⊒-refl {p = here px} = refl
∈-⊒-refl {p = there p} = cong there ∈-⊒-refl

∈-⊒-trans : ∀ {a}{A : Set a}{xs ys zs : List A}{x}{p : x ∈ xs}(q : ys ⊒ xs)(r : zs ⊒ ys) → ∈-⊒ p (⊑-trans q r) ≡ ∈-⊒ (∈-⊒ p q) r
∈-⊒-trans {p = here px} (x ∷ l) (.x ∷ r) = refl
∈-⊒-trans {p = there p} (x ∷ l) (.x ∷ r) = cong there (∈-⊒-trans l r)

open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Nullary

module Decidable {a}{A : Set a}(_≟_ : Decidable (_≡_ {A = A})) where

  _⊑?_ : Decidable (_⊑_ {A = A})
  [] ⊑? _ = yes []
  (x ∷ xs) ⊑? [] = no (λ ())
  (x ∷ xs) ⊑? (y ∷ ys) with x ≟ y
  (x ∷ xs) ⊑? (y ∷ ys) | no ¬p = no (λ{ (.x ∷ z) → ¬p refl })
  (x ∷ xs) ⊑? (.x ∷ ys) | yes refl with xs ⊑? ys
  ... | yes px = yes (x ∷ px)
  ... | no ¬px = no (λ{ (.x ∷ px) → ¬px px})

  _⊒?_ : Decidable (_⊒_ {A = A})
  xs ⊒? ys = ys ⊑? xs

import Relation.Binary.PropositionalEquality.Core as PC
⊑-preorder : ∀ {ℓ}{A : Set ℓ} → Preorder ℓ ℓ ℓ
⊑-preorder {A = A} = record {
  Carrier = List A ; _≈_ = _≡_ ; _∼_ = _⊑_ ;
  isPreorder = record {
    isEquivalence = ≡.isEquivalence ;
    reflexive = λ{ refl → ⊑-refl } ; trans = ⊑-trans } }

⊒-preorder : ∀ {ℓ}{A : Set ℓ} → Preorder _ _ _
⊒-preorder {A = A} = record {
  Carrier = List A ; _≈_ = _≡_ ; _∼_ = _⊒_ ;
  isPreorder = record {
    isEquivalence = ≡.isEquivalence ;
    reflexive = λ{ refl → ⊑-refl } ; trans = λ p q → ⊑-trans q p } }
