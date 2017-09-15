open import MJ.Types
import MJ.Classtable.Core as Core

module MJ.Syntax.Typed {c}(Ct : Core.Classtable c) where

open import Prelude hiding (erase)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Maybe.All as MayAll
open import Data.Vec as Vec hiding (_∈_)
open import Data.Star as Star
open import Data.List.Most as List
open import Data.List.Properties.Extra as List+
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Data.String

import Data.Vec.All as Vec∀

open Core c
open Classtable Ct
open import MJ.Classtable.Membership Ct
open import MJ.LexicalScope Ct

NativeBinOp = ℕ → ℕ → ℕ

data Expr (Γ : Ctx) : Ty c → Set where
  -- irreducible expressions
  unit     : Expr Γ void
  null     : ∀ {C} → Expr Γ (ref C)
  num      : ℕ → Expr Γ int

  -- storeless expressions
  var      : ∀ {a} → Var Γ a → Expr Γ a
  iop      : NativeBinOp → (l r : Expr Γ int) → Expr Γ int
  upcast   : ∀ {c c'} → Σ ⊢ c <: c' → Expr Γ (ref c) → Expr Γ (ref c')
  -- downcast : ∀ {c c'} → Σ ⊢ c' <: c → Expr Γ (ref c) → Expr Γ (ref c')

  -- storefull
  new      : ∀ C → All (Expr Γ) (Class.constr (Σ C)) → Expr Γ (ref C)
  call     : ∀ {cid} →
             Expr Γ (ref cid) → ∀ m {as}{b}{acc : AccMember cid METHOD m (as , b)} → All (Expr Γ) as →
             Expr Γ b
  get      : ∀ {cid} → Expr Γ (ref cid) → ∀ f {ty}{acc : AccMember cid FIELD f ty} → Expr Γ ty

mutual
  data Stmt (I : Ctx)(r : Ty c) : (O : Ctx) → Set where
    loc        : ∀ a → Stmt I r (I +local a)
    asgn       : ∀ {a} → Var I a → Expr I a → Stmt I r I
    set        : ∀ {C} → Expr I (ref C) → ∀ f {a}{acc : AccMember C FIELD f a} → Expr I a → Stmt I r I
    do         : ∀ {a} → Expr I a → Stmt I r I
    ret        : Expr I r → Stmt I r I
    raise      : Stmt I r I
    try_catch_ : ∀ {O O'} → Stmt I r O → Stmt I r O' → Stmt I r I
    while_do_  : ∀ {O} → Expr I int → Stmt I r O → Stmt I r I
    block      : ∀ {O} → Stmts I r O → Stmt I r I

  Stmts : Ctx → Ty c → Ctx → Set
  Stmts I r O = Star (λ I' O' → Stmt I' r O') I O

postulate wkₑ : ∀ {Γ δ a} → Expr Γ a → Expr (Γ List.++ δ) a
postulate wkₛ : ∀ {I O δ a} → Stmt I a O → Stmt (I List.++ δ) a (O List.++ δ)
