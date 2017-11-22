module Categorical.Cofe.Products where

import Data.Unit as Unit
open import Data.Product

open import Level
open import Categories.Functor.Core
open import Categories.Category
open import Categories.Product
open import Categories.FunctorCategory
open import Categories.Object.BinaryProducts
open import Categories.Object.Product
open import Categories.Object.Products
open import Categories.Object.Terminal
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Monoidal
open import Categories.Monoidal.Cartesian

open import Categorical.Functor.Const
open import Categorical.Cofe
open import Categorical.Ofe
import Categorical.Ofe.Products as OfeProd

open Category
open Cofe

module _ {o e e'} where

  module ⊤-Ofe = Terminal (OfeProd.⊤ {o}{e}{e'})

  open Terminal
  terminal : Terminal (Cofes {o}{e}{e'})
  ⊤ terminal = record
    { ofe = ⊤-Ofe.⊤
    ; conv = λ c → lim (lift Unit.tt) λ n → lift Unit.tt
    }
  ! terminal = record
    { _⟨$⟩_ = λ _ → lift Unit.tt
    ; cong = λ _ → lift Unit.tt }
  !-unique terminal = λ _ _ → lift Unit.tt

module _ {o e e'}(A B : Cofe o e e') where

  _×-Cofe_ : Obj (Cofes {o}{e}{e'})
  _×-Cofe_ = record
    { ofe = (ofe A) OfeProd.×-ofe (ofe B)
    ; conv = λ c →
      let
        l = conv A (chain-map (OfeProd.π₁ (ofe A) (ofe B)) c)
        r = Cofe.conv B (chain-map (OfeProd.π₂ (ofe A) (ofe B)) c)
      in lim (at-∞ l , at-∞ r) (λ n → limit l n , limit r n) }

open BinaryProducts
binary-products : ∀ {o e e'} → BinaryProducts (Cofes {o}{e}{e'})
product (binary-products {o}{e}{e'}) {A} {B} = record {
  A×B = A ×-Cofe B
  ; π₁ = OfeProd.π₁ (ofe A) (ofe B)
  ; π₂ = OfeProd.π₂ (ofe A) (ofe B)
  ; ⟨_,_⟩ = OfeProd.⟨_,_⟩ (ofe A) (ofe B)
  ; commute₁ = λ {_}{f}{g} → ×Ofe.commute₁ {f = f}{g}
  ; commute₂ = λ {_}{f}{g} → ×Ofe.commute₂ {f = f}{g}
  ; universal = λ{_}{f}{g}{i} → ×Ofe.universal {f = f}{g}{i} }
  where module ×Ofe = BinaryProducts (OfeProd.binary-products {o}{e}{e'})

products : ∀ {o e e'} → Products (Cofes {o}{e}{e'})
products = record
  { terminal = terminal
  ; binary = binary-products }

monoidal : ∀ {o e e'} → Monoidal (Cofes {o}{e}{e'})
monoidal = Cartesian _ products
