open import MJ.Types
import MJ.Classtable.Core as Core

{-
MJMinor bubbles up all side-effects to separate "statements";
such that the order of side-effects is made entirely explicit in
the imperative structure of the program.

We identify 4 syntactical constructs:
1. Expr: pure expressions
2. Expr⁺: effectful expressions
3. Cmd: effectful commands
4. Block
-}
module MJMinor.Syntax.Typed {c}(Ct : Core.Classtable c) where

open import Prelude hiding (erase)
open import Data.Sum
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Maybe.All as MayAll
open import Data.Vec as Vec hiding (_∈_)
open import Data.List.Most as List
open import Data.List.Any.Properties
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

-- subset of expressions that do not update the state
data Expr (Γ : Ctx) : Ty c → Set where
  unit     : Expr Γ void
  null     : ∀ {C} → Expr Γ (ref C)
  num      : ℕ → Expr Γ int
  var      : ∀ {a} → Var Γ a → Expr Γ a
  iop      : NativeBinOp → (l r : Expr Γ int) → Expr Γ int
  upcast   : ∀ {c c'} → Σ ⊢ c <: c' → Expr Γ (ref c) → Expr Γ (ref c')
  get      : ∀ {cid} → Expr Γ (ref cid) → ∀ f {ty}{acc : AccMember cid FIELD f ty} → Expr Γ ty

data Exception (Γ : Ctx) : Ty c → Set where
  ret       : ∀ {r} → Expr Γ r → Exception Γ r
  unchecked : ∀ {r} → Exception Γ r

data Cmd (Γ : Ctx)(r : Ty c) : Ty c → Set where
  val        : ∀ {a} → Expr Γ a → Cmd Γ r a
  call       : ∀ {cid} →
                Expr Γ (ref cid) → ∀ m {as}{b}{acc : AccMember cid METHOD m (as , b)} →
                All (Expr Γ) as →
                Cmd Γ r b
  new        : ∀ C → All (Expr Γ) (Class.constr (Σ C)) → Cmd Γ r (ref C)
  asgn       : ∀ {a} → Var Γ a → Expr Γ a → Cmd Γ r void
  set        : ∀ {C} → Expr Γ (ref C) → ∀ f {a}{acc : AccMember C FIELD f a} → Expr Γ a → Cmd Γ r void
  raise      : Exception Γ r → Cmd Γ r void

infixr 30 _◅◅_
infixl 50 _◅_
data Block (I : Ctx)(r : Ty c): Ty c → Set where
  •⟨_⟩ : ∀ {a} → Expr I a → Block I r a
  _◅_  : ∀ {a b} → Cmd I r a → Block (a ∷ I) r b → Block I r b
  _◅◅_  : ∀ {a b} → Block I r a → Block (a ∷ I) r b → Block I r b
  seq : ∀ {a b} → Block I r a → Block I r b → Block I r b
  try_catch_◅_ : ∀ {a b c} → Block I r a → Block I r b → Block I r c → Block I r c
  while_do_◅_ : ∀ {a b c} → Block I r a → Block I r b → Block I r c → Block I r c
