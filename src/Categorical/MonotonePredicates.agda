open import Categorical.Preorder

module Categorical.MonotonePredicates {ℓ₂ ℓ₃} (po : PreorderPlus ℓ₃ ℓ₂ ℓ₃) where

open import Categories.Category
open import Categories.Monoidal
open import Categories.FunctorCategory

open import Categorical.FunctorCategory.Products
open import Categorical.Cofe
open import Categorical.Cofe.Products using () renaming (products to cofe-products)

MP : ∀ {o e e'} → Category _ _ _
MP {o}{e}{e'} = Functors (Preorder po) (Cofes {o}{e}{e'})

is-monoidal : ∀ {o e e'} → Monoidal (MP {o}{e}{e'})
is-monoidal = monoidal _ _ cofe-products
