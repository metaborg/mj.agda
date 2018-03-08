open import MJ.Types as Types
import MJ.Classtable.Core as Core

module MJ.Semantics.Values {c}(Ct : Core.Classtable c) where

open import Prelude

open import Level renaming (suc to lsuc; zero to lzero)
open import Data.Integer as Int
open import Data.List.Most
open import Data.List.Prefix
open import Relation.Nullary.Decidable
open import Relation.Unary.Monotone

open Core c
open Classtable Ct
open import MJ.Classtable.Membership Ct
open import MJ.LexicalScope c
{-
MJ inherits the values of STLC+Ref. In contrast to STCL+Ref, MJ also has
null-pointers; which we add as a constructor to our value type Val. The value
constructed by null is typed with an arbitrary reference type as it can be used
in place of any proper reference.
-}
data Val (W : World c) : Ty c → Set where
  bool : Bool → Val W bool
  num  : ℤ → Val W int
  unit : Val W void
  null : ∀ {C} → Val W (ref C)
  ref  : ∀ {C P} → (obj C) ∈ W → Σ ⊢ C <: P → Val W (ref P)

open import Data.String as Str
show-val : ∀ {W a} → Val W a → String
show-val (num x)      = "num " Str.++ Int.show x
  where import Data.Integer as Int
show-val unit         = "unit"
show-val null         = "NULL"
show-val (bool true)  = "true"
show-val (bool false) = "false"
show-val (ref _ _)    = "ref _"

-- equality on values
infixl 30 _≟val⟨_⟩_
_≟val⟨_⟩_ : ∀ {W : World c}{a b} → Val W a → a <:< b → Val W b → Bool
(num x) ≟val⟨ int ⟩ (num y)            = ⌊ (x Int.≟ y) ⌋
  where open import Data.Nat as Nat
(bool true) ≟val⟨ bool ⟩ (bool true)   = true
(bool true) ≟val⟨ bool ⟩ (bool false)  = false
(bool false) ≟val⟨ bool ⟩ (bool true)  = false
(bool false) ≟val⟨ bool ⟩ (bool false) = true
unit ≟val⟨ void ⟩ unit                 = true
null ≟val⟨ cls x ⟩ null                = true
null ≟val⟨ cls x ⟩ ref x₁ x₂           = false
(ref _ _) ≟val⟨ cls _ ⟩ null           = false
(ref x _) ≟val⟨ cls _ ⟩ (ref y _)      = ⌊ (index x) Fin.≟ (index y) ⌋
  where
    import Data.Fin.Properties as Fin

{-
We can construct default values out of thin air for every type
-}
default : ∀ {W} → (a : Ty c) → Val W a
default void    = unit
default int     = num (+ 0)
default (ref x) = null
default bool    = bool false

{-
Value weakening
-}
weaken-val : ∀ {a}{W W' : World c} → W ⊒ W' → Val W' a → Val W a
weaken-val ext (num n)     = num n
weaken-val ext unit        = unit
weaken-val ext null        = null
weaken-val ext (bool b)    = bool b
weaken-val ext (ref x sub) = ref (∈-⊒ x ext) sub

instance
  val-weakenable : ∀ {a} → Monotone ⊑-preorder (λ W → Val W a)
  val-weakenable = record { wk = weaken-val }

data Exception : Set where
  nullderef : Exception
  other     : Exception
