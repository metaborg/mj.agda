module Category.Monad.Maybe.Typeclass where

open import Category.Monad
open import Data.Maybe

record MaybeMonad (M : Set → Set) : Set₁ where
  field
    no  : ∀ {A} → M A
    yes : ∀ {A} → A → M A

open MaybeMonad
maybe-monad-ops : MaybeMonad Maybe
no  maybe-monad-ops = nothing
yes maybe-monad-ops = just
