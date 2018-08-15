open import MJ.Types as Types
import MJ.Classtable.Core as Core

module MJ.Semantics.Objects {c}(Ct : Core.Classtable c) where

open import Prelude

open import Level renaming (suc to lsuc; zero to lzero)
open import Data.List.Most
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

  sval-weaken : ∀ {W W' a} → W' ⊒ W → StoreVal W a → StoreVal W' a
  sval-weaken ext (val x) = val $ weaken-val ext x
  sval-weaken ext (obj cid x) = obj cid (weaken-obj cid ext x)

  open import Relation.Binary using (Preorder)
  open import Relation.Unary.Monotone (⊑-preorder {A = Ty⁺ c})

  instance
    open Monotone
    storeval-monotone : ∀ {a} → Monotone (λ W → StoreVal W a)
    wk storeval-monotone = sval-weaken
