module Data.Star.Indexed where

open import Relation.Binary
open import Function
open import Level

infixr 10 _◅_
data Star {i a t}(I : Set i){A : I → Set a}
     (T : ∀ n m → REL (A n) (A m) t) : ∀ {n m : I} → REL (A n) (A m) (i ⊔ a ⊔ t) where
  ε   : ∀ {i}{x : A i} → Star I T x x
  _◅_ : ∀ {n m k : I}{x : A n}{y : A m}{z : A k} → T n m x y → Star I T y z → Star I T x z
