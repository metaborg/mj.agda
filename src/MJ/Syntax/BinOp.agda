import MJ.Classtable.Core as Core

module MJ.Syntax.BinOp {c}(Ct : Core.Classtable c) where

open import Data.Sum
open import Data.Maybe

open import MJ.Types

open Core c
open Classtable Ct

data BinOp : (a b c : Ty c)  → Set where
  == !=          : ∀ {a b} → (a <:< b) ⊎ (b <:< a) → BinOp a b bool
  < <= > >=      : BinOp int int bool
  + - *          : BinOp int int int
  orb xorb andb  : BinOp bool bool bool
