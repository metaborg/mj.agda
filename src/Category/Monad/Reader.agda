module Category.Monad.Reader {i}{I : Set i} where

open import Category.Applicative.Indexed
open import Category.Monad
open import Category.Monad.Predicate
open import Relation.Unary
open import Relation.Unary.PredicateTransformer
open import Data.Product
open import Data.Unit
open import Function
open import Level

ReaderT : Set i → Pt I i → Pt I i
ReaderT E M P = λ i → E → M P i

module ReaderT (E : Set i){M : Pt I i}(Mon : RawPMonad {ℓ = i} M) where

  module Mon = RawPMonad Mon

  open RawPMonad
  reader : RawPMonad {ℓ = i} (ReaderT E M)
  return? reader x e = Mon.return? x
  _=<?_  reader f m e = (λ x → f x e) Mon.=<? m e

  -- operations
  ask : ∀ {i : I} → ReaderT E M (λ _ → E) i
  ask E = return? Mon E

  asks : ∀ {A}{i : I} → (E → A i) → ReaderT E M A i
  asks f E = return? Mon (f E)

  local : ∀ {E'}{A}{i : I} → E' → ReaderT E' M A i → ReaderT E M A i
  local e' m = λ _ → m e'
