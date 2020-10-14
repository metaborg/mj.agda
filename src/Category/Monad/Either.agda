module Category.Monad.Either {i}(Exc : Set i)(I : Set i) where

open import Level hiding (lift)
open import Data.Sum

open import Category.Monad
open import Category.Monad.Predicate
open import Relation.Unary
open import Relation.Unary.PredicateTransformer


pattern left x = inj₁ x
pattern right x = inj₂ x

EitherT : Pt I i → Pt I i
EitherT M P = M (λ i → Exc ⊎ P i)

module EitherT {M : Pt I i}(Mon : RawPMonad {ℓ = i} M) where

  private module Mon = RawPMonad Mon

  -- right-biased sum
  open RawPMonad
  monad : RawPMonad {ℓ = i} (EitherT M)
  return? monad px = Mon.return? (right px)
  _=<?_ monad {P}{Q} f px = g Mon.=<? px
    where
      g : (λ i → Exc ⊎ P i) ⊆ EitherT M Q
      g (left x) = Mon.return? (left x)
      g (right y) = f y

  _recoverWith_ : ∀ {P i} → EitherT M P i → (∀ {i} → Exc → EitherT M P i) → EitherT M P i
  _recoverWith_ {P} c f = g Mon.=<? c
    where
      g : (λ i → Exc ⊎ P i) ⊆ EitherT M P
      g (left x) = f x
      g (right y) = Mon.return? (right y)

  lift : ∀ {P} → M P ⊆ EitherT M P
  lift x = (λ z → Mon.return? (right z)) Mon.=<? x
