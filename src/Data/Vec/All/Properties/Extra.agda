module Data.Vec.All.Properties.Extra {a p}{A : Set a}{P : A → Set p} where

open import Data.List using (List)
open import Data.List.All as List∀ using ()
open import Data.Vec hiding (_[_]≔_)
open import Data.Vec.All hiding (lookup)
open import Data.Fin

all-fromList : ∀ {xs : List A} → List∀.All P xs → All P (fromList xs)
all-fromList List∀.[] = []
all-fromList (px List∀.∷ p) = px ∷ all-fromList p

_[_]≔_ : ∀ {n}{l : Vec A n} → All P l → (i : Fin n) → P (lookup i l)→ All P l
[] [ () ]≔ px
(px ∷ l) [ zero ]≔ px₁ = px₁ ∷ l
(px ∷ l) [ suc i ]≔ px₁ = px ∷ (l [ i ]≔ px₁)
