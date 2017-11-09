module Categorical.ISetoids.Product where

open import Categories.Functor
open import Categories.Bifunctor
open import Categories.Agda
open import Categories.Category
open import Categories.Support.Equivalence
open import Categories.Support.SetoidFunctions
open import Categories.Object.Product

open import Data.Product
open import Function as Fun

open Functor
open _⟶_

-- the product bifunctor
-- TODO use the construction Cartesian from the lib
A×BSetoid : ∀ s₁ s₂ → Bifunctor (ISetoids s₁ s₂) (ISetoids s₁ s₂) (ISetoids s₁ s₂)
F₀ (A×BSetoid s₁ s₂) (A , B) = A ×-setoid B
_⟨$⟩_ (F₁ (A×BSetoid s₁ s₂) (f , g)) (x , y) = f ⟨$⟩ x , g ⟨$⟩ y
cong (F₁ (A×BSetoid s₁ s₂) (f , g)) (x , y) = cong f x , cong g y
identity (A×BSetoid s₁ s₂) = Fun.id
homomorphism (A×BSetoid s₁ s₂) {f = f , f'} {g , g'} (x≡x' , y≡y') =
  cong (ISetoids _ _ [ g ∘ f ]) x≡x' , cong (ISetoids _ _ [ g' ∘ f' ]) y≡y'
F-resp-≡ (A×BSetoid s₁ s₂) (f≡f' , g≡g') (x≡x' , y≡y') = (f≡f' x≡x') , (g≡g' y≡y')
