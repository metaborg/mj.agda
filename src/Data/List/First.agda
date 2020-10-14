module Data.List.First {ℓ}{A : Set ℓ} where

open import Data.Product
open import Data.List
open import Data.List.Any
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Level
open import Function
open import Data.Empty

-- proof that an element is the first in a vector to satisfy the predicate B
data First {b}(B : A → Set b) : (x : A) → List A → Set (ℓ ⊔ b) where

  here  : ∀ {x : A} → (p : B x) → {v : List A} → First B x (x ∷ v)
  there : ∀ {x} {v : List A} (x' : A) → ¬ (B x') → First B x v → First B x (x' ∷ v)

-- get the witness of B x from the element ∈ First
first⟶witness : ∀ {B : A → Set} {x l} → First B x l → B x
first⟶witness (here p) = p
first⟶witness (there x ¬px f) = first⟶witness f

-- more likable syntax for the above structure
first_∈_⇒_ : ∀ {p} → A → List A → (B : A → Set p) → Set (p ⊔ ℓ)
first_∈_⇒_ x v p = First p x v

-- a decision procedure to find the first element in a vector that satisfies a predicate
find : ∀ (P : A → Set) → ((a : A) → Dec (P a)) → (v : List A) →
       Dec (∃ λ e → first e ∈ v ⇒ P)
find P dec [] = no (λ{ (e , ()) })
find P dec (x ∷ v) with dec x
find P dec (x ∷ v) | yes px = yes (x , here px)
find P dec (x ∷ v) | no ¬px with find P dec v
find P dec (x ∷ v) | no ¬px | yes firstv = yes (, there x ¬px (proj₂ firstv))
find P dec (x ∷ v) | no ¬px | no ¬firstv = no $ helper ¬px ¬firstv
  where
    helper : ¬ (P x) → ¬ (∃ λ e → First P e v) → ¬ (∃ λ e → First P e (x ∷ v))
    helper ¬px ¬firstv (.x , here p) = ¬px p
    helper ¬px ¬firstv (u  , there ._ _ firstv) = ¬firstv (u , firstv)
