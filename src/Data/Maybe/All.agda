module Data.Maybe.All {a}{A : Set a} where

open import Data.Maybe hiding (map)

map : ∀ {p q}{P : A → Set p}{Q : A → Set q}{x} → (∀ {x} → P x → Q x) → All P x → All Q x
map f (just px) = just (f px)
map f nothing = nothing

all : ∀ {p}{P : A → Set p} → (∀ (x : A) → P x) → (x : Maybe A) → All P x
all f (just x) = just (f x)
all f nothing = nothing
