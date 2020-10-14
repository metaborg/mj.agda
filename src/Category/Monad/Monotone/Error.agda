open import Relation.Binary hiding (_⇒_)

module Category.Monad.Monotone.Error {i}(pre : Preorder i i i)(Exc : Set i) where

open Preorder pre renaming (Carrier to I; _∼_ to _≤_; refl to ≤-refl)

open import Function
open import Level hiding (lift)
open import Data.Sum

open import Relation.Unary
open import Relation.Unary.Monotone pre
open import Relation.Unary.PredicateTransformer

open import Category.Monad.Monotone pre
open import Category.Monad.Monotone.Identity pre

pattern left x = inj₁ x
pattern right x = inj₂ x

ErrorT : Pt I i → Pt I i
ErrorT M P = M (λ i → Exc ⊎ P i)

Error = ErrorT Identity

record ErrorMonad (M : Pt I i) : Set (suc i) where
  field
    throw : ∀ {P i} → Exc → M P i
    try_catch_ : ∀ {P}   → M P ⊆ ((const Exc ↗ M P) ⇒ M P)

module _ {M} ⦃ Mon : RawMPMonad M ⦄ where
  private module M = RawMPMonad Mon

  open RawMPMonad
  errorT-monad : RawMPMonad (ErrorT M)
  return errorT-monad px = M.return (right px)
  _≥=_ errorT-monad {P}{Q} px f = px M.≥= λ where
      _ (left e)  → M.return (left e)
      w (right x) → f w x

  open ErrorMonad
  errorT-monad-ops : ErrorMonad (ErrorT M)
  throw errorT-monad-ops e = M.return (left e)
  try_catch_ errorT-monad-ops c f = c M.≥= λ where
    w (left e)  → f w e
    w (right x) → M.return (right x)

  lift-error : ∀ {P} → M P ⊆ ErrorT M P
  lift-error x = x M.>>= (λ z → M.return (right z))

module Instances where
  -- Defining instances for the transformer
  -- leads to divergence of instance search,
  -- because M is on the outside.
  instance
    open RawMPMonad
    error-monad : RawMPMonad Error
    error-monad = errorT-monad

    open ErrorMonad
    error-monad-ops : ErrorMonad Error
    error-monad-ops = errorT-monad-ops
