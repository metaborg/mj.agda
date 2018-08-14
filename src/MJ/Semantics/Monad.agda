import MJ.Classtable

open import Level renaming (zero to ℓz) hiding (lift)
import MJ.Classtable.Core as Core

module MJ.Semantics.Monad {c} (Ct : Core.Classtable c) (Exc : Set) where

open import Prelude hiding (_^_; _+_)
open import Function
open import Data.List.Most as List
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Relation.Binary using (Preorder)
open import Relation.Unary hiding (_∈_)
open import Relation.Unary.PredicateTransformer using (Pt)

open import MJ.Types
open import MJ.LexicalScope
open import MJ.Semantics.Objects Ct
open import MJ.Semantics.Environments Ct
open import MJ.Semantics.Objects.Flat Ct using (encoding)
open ObjEncoding encoding

private pre = ⊑-preorder {A = Ty⁺ c}
open Preorder pre renaming (Carrier to I; _∼_ to _≤_; refl to ≤-refl)

open import Relation.Unary.Monotone pre
open import Relation.Unary.Monotone.Prefix
open import Category.Monad.Monotone pre
open import Category.Monad.Monotone.Heap pre (Ty⁺ c) (flip StoreVal) Store _∈_
open import Category.Monad.Monotone.Heap.HList (Ty⁺ c) (flip StoreVal)
open import Category.Monad.Monotone.Reader pre
open import Category.Monad.Monotone.Error pre
open import Category.Monad.Monotone.State ⊑-preorder Store

M : Pred (World c) ℓz → Pt (World c) ℓz
M E = ErrorT Exc (ReaderT E (MST Maybe))

instance
  open import Category.Monad
  maybe-monad : RawMonad {f = ℓz} Maybe
  maybe-monad = Maybe.monad

module _ E ⦃ mono-E : Monotone E ⦄ where
  -- gotta help instance search a bit
  private
    instance
      inner : RawMPMonad (ReaderT E (MST Maybe))
      inner = reader-monad

      inner-has-reader : ReaderMonad E (λ E → ReaderT E (MST Maybe))
      inner-has-reader = reader-monad-ops

  monad : RawMPMonad (M E)
  monad = errorT-monad Exc

  private
    instance
      monad-instance : RawMPMonad (M E)
      monad-instance = errorT-monad Exc

  timeout : ∀ {P i} → M E P i
  timeout _ _ = nothing

  m-has-reader : ReaderMonad E M
  ReaderMonad.ask m-has-reader = lift-error Exc (ReaderMonad.ask inner-has-reader)
  ReaderMonad.reader m-has-reader f = lift-error Exc (ReaderMonad.reader inner-has-reader f)
  ReaderMonad.local m-has-reader _ f m E = m (f E)

  m-has-mst : StateMonad (M E)
  StateMonad.runState m-has-mst f = lift-error Exc (lift-reader E (StateMonad.runState mst-monad-ops f))

  postulate m-has-heap : HeapMonad (M E)
  {-}
  HeapMonad.super m-has-heap = m-has-mst
  HeapMonad.store m-has-heap = lift-error (lift-reader E (HeapMonad.store hlist-heap-monad))
  HeapMonad.modify m-has-heap = {!!}
  HeapMonad.deref m-has-heap = {!!}
  -}

  m-has-error : ErrorMonad Exc (M E)
  m-has-error = errorT-monad-ops Exc

  open ErrorMonad
  m-has-timeout : ErrorMonad ⊤ (M E)
  throw m-has-timeout _ _ _ = nothing
  try_catch_ m-has-timeout m f E μ = case m E μ of λ where
    nothing → f ≤-refl tt E μ
    (just x)  → just x
