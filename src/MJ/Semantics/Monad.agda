import MJ.Classtable

open import Level renaming (zero to ℓz) hiding (lift)
import MJ.Classtable.Core as Core

module MJ.Semantics.Monad {c} (Ct : Core.Classtable c) (Exc : Set) where

open import Prelude hiding (_^_; _+_)
open import Data.List.Most as List hiding (_⊆_)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Relation.Unary.PredicateTransformer using (Pt)

open import MJ.Types
open import MJ.LexicalScope
open import MJ.Semantics.Objects Ct
open import MJ.Semantics.Environments Ct
open import MJ.Semantics.Objects.Flat Ct using (encoding)
open ObjEncoding encoding

pre = ⊑-preorder {A = Ty⁺ c}

open import Relation.Unary.Monotone pre
open import Relation.Unary.Monotone.Prefix
open import Category.Monad.Monotone pre
open import Category.Monad.Monotone.State.HList (Ty⁺ c) (flip StoreVal)
open import Category.Monad.Monotone.Reader pre
open import Category.Monad.Monotone.Error Exc pre
open import Category.Monad.Monotone.State ⊑-preorder Store
open import Category.Monad.Monotone.State.HList

M : Ctx c → Pt (World c) ℓz
M Γ = ErrorT (ReaderT (Env Γ) (MST Maybe))

instance
  open import Category.Monad
  maybe-monad : RawMonad {f = ℓz} Maybe
  maybe-monad = Maybe.monad

module _ {Γ} where
  -- gotta help instance search a bit
  private
    Inner = (ReaderT (Env Γ) (MST Maybe))
    instance
      inner : RawMPMonad Inner
      inner = reader-monad (Env Γ)

      inner-has-reader = reader-monad-ops (Env Γ)

  timeout : ∀ {P i} → M Γ P i
  timeout _ _ = nothing

  instance
    m-has-reader : ReaderMonad (Env Γ) (M Γ)
    ReaderMonad.ask m-has-reader = lift-error ask
    ReaderMonad.reader m-has-reader f = lift-error (reader f)
    ReaderMonad.local m-has-reader f m E = m (f E)

    m-has-mst : StateMonad (M Γ)
    StateMonad.runState m-has-mst f = lift-error (lift-reader (Env Γ) (runState f))

    m-has-error : ErrorMonad (M Γ)
    m-has-error = errorT-monad-ops
