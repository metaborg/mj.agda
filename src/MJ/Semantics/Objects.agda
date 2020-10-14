open import MJ.Types as Types
import MJ.Classtable.Core as Core

module MJ.Semantics.Objects {c}(Ct : Core.Classtable c) where

open import Prelude

open import Level renaming (suc to lsuc; zero to lzero)
open import Data.List
open import Data.List.Relation.Unary.All
open import Data.List.Prefix

open Core c
open Classtable Ct

open import MJ.Classtable.Membership Ct
open import MJ.Semantics.Values Ct
open import MJ.LexicalScope c

{-
Abstract interface for object encodings.
-}
record ObjEncoding : Set (lsuc lzero) where
  field
    Obj : World c → Cid c → Set
    weaken-obj : ∀ {W W'} cid → W' ⊒ W → Obj W cid → Obj W' cid
    getter : ∀ {W m a} c → Obj W c → IsMember c FIELD m a → Val W a
    setter : ∀ {W m a} c → Obj W c → IsMember c FIELD m a → Val W a → Obj W c
    defaultObject : ∀ {W} c → Obj W c

  data StoreVal (W : World c) : Ty⁺ c → Set where
    val : ∀ {ty} → Val W ty → StoreVal W (vty ty)
    obj : ∀ cid → Obj W cid → StoreVal W (obj cid)

  Store : World c → Set
  Store W = All (StoreVal W) W
