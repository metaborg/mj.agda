module Data.Fin.Properties.Extra where

open import Data.Fin hiding (_≤_)
open import Data.Nat
open import Data.Nat.Properties

open import Relation.Binary.PropositionalEquality

inject≤-trans : ∀ {l m n} i (p : l ≤ m)(q : m ≤ n) → inject≤ (inject≤ i p) q ≡ inject≤ i (≤-trans p q)
inject≤-trans () z≤n q
inject≤-trans zero (s≤s p) (s≤s q) = refl
inject≤-trans (suc i) (s≤s p) (s≤s q) = cong suc (inject≤-trans i p q)
