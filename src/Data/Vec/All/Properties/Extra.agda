module Data.Vec.All.Properties.Extra {a p}{A : Set a}{P : A → Set p} where

open import Data.List using (List)
import Data.List.Relation.Unary.All as All
open import Data.Vec hiding (_[_]≔_)
open import Data.Vec.Relation.Unary.All hiding (lookup)
open import Data.Fin

all-fromList : ∀ {xs : List A} → All.All P xs → All P (fromList xs)
all-fromList All.[] = []
all-fromList (px All.∷ p) = px ∷ all-fromList p

_[_]≔_ : ∀ {n}{l : Vec A n} → All P l → (i : Fin n) → P (lookup l i)→ All P l
[] [ () ]≔ px
(px ∷ l) [ zero ]≔ px₁ = px₁ ∷ l
(px ∷ l) [ suc i ]≔ px₁ = px ∷ (l [ i ]≔ px₁)
