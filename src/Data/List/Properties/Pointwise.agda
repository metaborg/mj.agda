module Data.List.Properties.Pointwise where

open import Data.Nat
open import Data.List
open import Relation.Binary.List.Pointwise hiding (refl; map)
open import Relation.Binary.PropositionalEquality

pointwise-∷ʳ : ∀ {a b ℓ A B P l m x y} → Rel {a} {b} {ℓ} {A} {B} P l m → P x y →
              Rel {a} {b} {ℓ} {A} {B} P (l ∷ʳ x) (m ∷ʳ y)
pointwise-∷ʳ [] q = q ∷ []
pointwise-∷ʳ (x∼y ∷ p) q = x∼y ∷ (pointwise-∷ʳ p q)

{-}
pointwise-[]≔ : ∀ {a b ℓ A B P l m i x y} →
                Rel {a} {b} {ℓ} {A} {B} P l m → (p : l [ i ]= x) → P x y →
                Rel {a} {b} {ℓ} {A} {B} P l (m [ fromℕ ([]=-length l p) ]≔ y)
pointwise-[]≔ r p q z = ?
postulate
pointwise-[]≔ [] () r
pointwise-[]≔ (x∼y ∷ r) here (s≤s z≤n) z = z ∷ r
pointwise-[]≔ (x∼y ∷ r) (there p) (s≤s q) z = subst (λ x → Rel _ _ x) {!!} (x∼y ∷ pointwise-[]≔ r p q z) 
-}

pointwise-length : ∀ {a b ℓ A B P l m} → Rel {a} {b} {ℓ} {A} {B} P l m → length l ≡ length m
pointwise-length [] = refl
pointwise-length (x∼y ∷ p) = cong suc (pointwise-length p)
