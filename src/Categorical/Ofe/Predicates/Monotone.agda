open import Categorical.Preorder

module Categorical.Ofe.Predicates.Monotone {p ℓ} (po : PreorderPlus p ℓ ℓ) where

open import Categories.Category
open import Categories.Monoidal
open import Categories.FunctorCategory
open import Categories.Object.Products

open import Categorical.FunctorCategory.Products renaming (monoidal to Fs-monoidal; products to Fs-products)
open import Categorical.Ofe
open import Categorical.Ofe.Products using () renaming (products to ofe-products)

MP : ∀ {o e e'} → Category _ _ _
MP {o}{e}{e'} = Functors (Preorder po) (Ofes {o}{e}{e'})

products : ∀ {o e e'} → Products (MP {o}{e}{e'})
products = Fs-products _ _ ofe-products

monoidal : ∀ {o e e'} → Monoidal (MP {o}{e}{e'})
monoidal = Fs-monoidal _ _ ofe-products
