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
    weaken-pair = record { weaken = λ{ ext (x , y) → (weaken ext x , weaken ext y) } }

  -- an alias
  _′_ : ∀ {i j}{W : Set}{p : W → Set i}{q : W → Set j}{w : W} → p w → q w → (p ⊗ q) w
  _′_ = _,_
