module Categorical.Cofe.Products where

import Data.Unit as Unit
open import Data.Product

open import Level
open import Categories.Functor.Core
open import Categories.Category
open import Categories.Product

open import Categorical.Cofe
open import Categorical.Ofe
open import Categorical.Ofe.Products

open Category
open Cofe

-- taking products of cofes preserves completeness
_×-cofe_ : ∀ {o e e'}(A B : Cofe o e e') → Cofe o e e'
A ×-cofe B = record
  { ofe = (ofe A) ×-ofe (ofe B)
  ; conv = λ c →
    let
      l = conv A (chain-map (π₁ (ofe A) (ofe B)) c)
      r = Cofe.conv B (chain-map (π₂ (ofe A) (ofe B)) c)
    in lim (at-∞ l , at-∞ r) (λ n → limit l n , limit r n) }
