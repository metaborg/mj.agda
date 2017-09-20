open import MJ.Types
import MJ.Classtable.Core as Core

module MJ.Syntax.Untyped {c}(Ct : Core.Classtable c) where

open import Prelude
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Maybe.All as MayAll
open import Data.Vec as Vec hiding (_∈_)
open import Data.Star
open import Data.List.Most
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Data.String

import Data.Vec.All as Vec∀

open Core c
open Classtable Ct
open import MJ.Classtable.Membership Ct
open import MJ.LexicalScope Ct

NativeBinOp = ℕ → ℕ → ℕ

data Expr (n : ℕ) : Set where
  new      : Cid c → List (Expr n) → Expr n
  unit     : Expr n
  null     : Expr n
  num      : ℕ → Expr n
  iop      : NativeBinOp → (l r : Expr n) → Expr n
  call     : Expr n → String → List (Expr n) → Expr n
  var      : Fin n → Expr n
  get      : Expr n → String → Expr n

mutual
  data Stmt (i : ℕ) : ℕ → Set where
    loc        : Ty c → Stmt i (suc i)
    asgn       : Fin i → Expr i → Stmt i i
    set        : Expr i → String → Expr i → Stmt i i
    do         : Expr i → Stmt i i
    ret        : Expr i → Stmt i i
    raise      : Stmt i i
    try_catch_ : ∀ {o o'} → Stmt i o → Stmt i o' → Stmt i i
    while_do_  : ∀ {o} → Expr i → Stmt i o → Stmt i i
    block      : ∀ {o} → Stmts i o → Stmt i i

  Stmts : ℕ → ℕ → Set
  Stmts = Star Stmt

data Body (i : ℕ) : Set where
  body : ∀ {o} → Stmts i o → Expr o → Body i

-- let n be the number of formal method arguments
data Method (n : ℕ) : Set where
  super⟨_⟩then_ : List (Expr (suc n)) → Body (suc (suc n)) → Method n
  body          : Body (suc n) → Method n

-- let n be the number of formal constructor arguments
data Constructor (n : ℕ) : Set where
  super_then_ : List (Expr (suc n)) → Body (suc n) → Constructor n
  body        : Body (suc n) → Constructor n

record Implementation (cid : _): Set where
  constructor implementation
  open Class (Σ cid) public
  field
    construct : Constructor (length constr)
    mbodies   : All (λ{ (name , (as , b)) → Method (length as) }) (decls METHOD)

Classes = ∀ cid → Implementation cid

Prog : Set
Prog = Classes × (Body 0)
