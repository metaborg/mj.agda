open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module Category.Monad.Monotone.Identity {i}(pre : Preorder i i i) where

open Preorder pre renaming (Carrier to I; _∼_ to _≤_; refl to ≤-refl)

open import Relation.Unary.PredicateTransformer using (Pt)
open import Category.Monad.Monotone pre
open RawMPMonad

Identity : Pt I i
Identity = λ P i → P i

instance
  id-monad : RawMPMonad Identity
  return id-monad px = px
  _≥=_ id-monad c f = f ≤-refl c
