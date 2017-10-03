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

{-
Expressions are indexed by a lexical context and a type.

MJ has n-ary calls for which we use All to express that an expression (of the
right type) is expected for every formal argument of the method signature.

In this nameless representation AccMember type is used to identify accessible
fields and methods on a particular class.
Here we exploit that AccMember is defined via a decision procedure: Agda
will be able to infer the membership proofs if they exist.
-}
data Expr (Γ : Ctx) : Ty c → Set where
  -- irreducible expressions
  unit     : Expr Γ void
  null     : ∀ {C} → Expr Γ (ref C)
  num      : ℕ → Expr Γ int

  -- storeless expressions
  var      : ∀ {a} → Var Γ a → Expr Γ a
  iop      : NativeBinOp → (l r : Expr Γ int) → Expr Γ int
  upcast   : ∀ {c c'} → Σ ⊢ c <: c' → Expr Γ (ref c) → Expr Γ (ref c')

  -- storeful
  new      : ∀ C → All (Expr Γ) (Class.constr (Σ C)) → Expr Γ (ref C)
  call     : ∀ {cid} →
             Expr Γ (ref cid) → ∀ m {as}{b}{acc : AccMember cid METHOD m (as , b)} → All (Expr Γ) as →
             Expr Γ b
  get      : ∀ {cid} → Expr Γ (ref cid) → ∀ f {ty}{acc : AccMember cid FIELD f ty} → Expr Γ ty

mutual
  {-
  Like Java, MJ distinguishes expressions from statements.
  We index the well-typed statement type Stmt
  with both an input and output context to capture that the constructor
  for declaration of locals loc adds to the lexical environment.
  We can interpret the type Stmt as a binary relation on contexts of which we
  can take the reflexive, transitive closure (Star)
  to obtain a datatype for sequenced statements:

  The type r represent the (possibly early) return type of a block of statements.
  -}
  infixl 20 if_then_else_
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
    if_then_else_ : ∀ {a} → Expr I int → Stmt I r a → Stmt I r a → Stmt I r a

  Stmts : Ctx → Ty c → Ctx → Set
  Stmts I r O = Star (λ I' O' → Stmt I' r O') I O
