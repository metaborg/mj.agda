module Categorical.ISetoids.Monads.Identity where

open import Function as Fun
open import Categories.Functor.Core renaming (id to idF)
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.Monad
open import Categories.Agda
open import Categories.Support.Equivalence
open import Categories.Support.SetoidFunctions as SF hiding (id)

open Monad

idM : ∀ {s₁ s₂} → Monad (ISetoids s₁ s₂)
F idM = idF
η idM = idN
μ idM = idN
assoc idM = Fun.id
identityˡ idM = Fun.id
identityʳ idM = Fun.id
