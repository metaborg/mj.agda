module Data.Vec.Extra where

open import Data.Product hiding (map; zip)
open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open import Function

map-with-∈ : ∀ {a}{A : Set a}{b n}{B : Set b}
             (xs : Vec A n) → (∀ i {x} → lookup i xs ≡ x → B) → Vec B n
map-with-∈ []       f = []
map-with-∈ (x ∷ xs) f = f zero refl ∷ map-with-∈ xs (λ i x → f (suc i) refl)
