module Data.Bool.Quantifiers where

open import Data.Unit
open import Data.Bool
open import Relation.Nullary public using (yes; no; ¬_; Dec)

data All {p} (P : Set p) : Bool → Set p where
  true  : P → All P true
  false : All P false

data Any {p} (P : Set p) : Bool → Set p where
  true  : P → Any P true

all-map : ∀ {p} {P Q : Set p} {b} → All P b → (f : P → Q) → All Q b
all-map (true x) f = true (f x)
all-map false f = false

Is-true : Bool → Set
Is-true t = Any ⊤ t

is-yes : ∀ {a} {A : Set a} → Dec A → Bool
is-yes (yes p) = true
is-yes (no ¬p) = false
