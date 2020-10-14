module Data.Fin.Subset.Disjoint where

open import Data.Nat
open import Data.Vec hiding (_∈_)
open import Data.Fin
open import Data.List as List hiding (zipWith)
open import Data.Fin.Subset

-- disjointness and relational specifiation of disjoint union
module _ {n} where

  _◆_ : Subset n → Subset n → Set
  l ◆ r = Empty (l ∩ r)

  data _⨄_ : List (Subset n) → Subset n → Set where
    []  : [] ⨄ ⊥
    _∷_ : ∀ {xs x y} → x ◆ y → xs ⨄ y → (x ∷ xs) ⨄ (x ∪ y)

-- picking from support
module _ {n} where
  _⊇⟨_⟩_ : Subset n → (l : ℕ) → Vec (Fin n) l → Set
  xs ⊇⟨ l ⟩ ys = All (λ y → y ∈ xs) ys
    where open import Data.Vec.All

-- removing from support
module _ {n} where
  _\\_ : ∀ {l} → Subset n → Vec (Fin n) l → Subset n
  xs \\ [] = xs
  xs \\ (x ∷ ys) = (xs [ x ]≔ outside) \\ ys
