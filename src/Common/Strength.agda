open import Agda.Primitive
open import Data.List.Most
open import Common.Weakening

module Common.Strength where

  open Weakenable ⦃...⦄

  data _⊗_ {i j}{W : Set} (p : W → Set i) (q : W → Set j) (w : W) : Set (i ⊔ j) where
    _,_ : p w → q w → (p ⊗ q) w

  instance
    weaken-pair : ∀ {i j}{A : Set}{p : List A → Set i}{q : List A → Set j}
                    ⦃ wp : Weakenable p ⦄ ⦃ wq : Weakenable q ⦄ →
                    Weakenable (p ⊗ q)
    weaken-pair = record { wk = λ{ ext (x , y) → (wk ext x , wk ext y) } }

  -- an alias
  infixr 10 _′_
  _′_ : ∀ {i j}{W : Set}{p : W → Set i}{q : W → Set j}{w : W} → p w → q w → (p ⊗ q) w
  _′_ = _,_

