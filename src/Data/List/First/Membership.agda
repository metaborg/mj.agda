module Data.List.First.Membership {ℓ}{A : Set ℓ} where

open import Data.Product
open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.List.First hiding (find)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Level
open import Function
open import Data.Empty

_∈_ : A → List A → Set _
x ∈ l = first x ∈ l ⇒ (_≡_ x)

¬x∈[] : ∀ {x} → ¬ x ∈ []
¬x∈[] ()

find : Decidable (_≡_ {A = A}) → ∀ x l → Dec (x ∈ l)
find _≟_ x [] = no (λ ())
find _≟_ x (y ∷ l) with x ≟ y
... | yes refl = yes (here refl)
... | no  neq  with find _≟_ x l
... | yes p    = yes (there y neq p)
... | no  ¬p   = no (λ{ (here eq) → neq eq ; (there _ _ p) → ¬p p})
