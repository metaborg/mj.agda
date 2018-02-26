open import MJ.Types as Types
import MJ.Classtable.Core as Core

module MJ.Semantics.Values {c}(Ct : Core.Classtable c) where

open import Prelude

open import Level renaming (suc to lsuc; zero to lzero)
open import Data.List.Most
open import Data.List.Prefix

open Core c
open Classtable Ct
open import MJ.Classtable.Membership Ct
open import MJ.LexicalScope c
open import Common.Weakening

{-
MJ inherits the values of STLC+Ref. In contrast to STCL+Ref, MJ also has
null-pointers; which we add as a constructor to our value type Val. The value
constructed by null is typed with an arbitrary reference type as it can be used
in place of any proper reference.
-}
data Val (W : World c) : Ty c → Set where
  num  : ℕ → Val W int
  unit : Val W void
  null : ∀ {C} → Val W (ref C)
  ref  : ∀ {C P} → (obj C) ∈ W → Σ ⊢ C <: P → Val W (ref P)

open import Data.String as Str
show-val : ∀ {W a} → Val W a → String
show-val (num x) = "num " Str.++ Nat.show x
  where import Data.Nat.Show as Nat
show-val unit = "unit"
show-val null = "NULL"
show-val (ref _ _) = "ref _"

{-
We can construct default values out of thin air for every type
-}
default : ∀ {W} → (a : Ty c) → Val W a
default void = unit
default int = num 0
default (ref x) = null

{-
Value weakening
-}
weaken-val : ∀ {a}{W W' : World c} → W ⊒ W' → Val W' a → Val W a
weaken-val ext (num n) = num n
weaken-val ext unit = unit
weaken-val ext null = null
weaken-val ext (ref x sub) = ref (∈-⊒ x ext) sub

instance
  val-weakenable : ∀ {a} → Weakenable (λ W → Val W a)
  val-weakenable = record { wk = weaken-val }

