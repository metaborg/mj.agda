open import MJ.Types
import MJ.Classtable.Core as Core

module MJ.Syntax.Erase {c}(Ct : Core.Classtable c) where

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
open import MJ.Classtable.Code Ct
open import MJ.LexicalScope Ct
open import MJ.Syntax.Typed Ct
open import MJ.Syntax.Program Ct
import MJ.Syntax.Untyped Ct as AST

{-# TERMINATING #-}
erase-expr : ∀ {Γ a} → Expr Γ a → AST.Expr (length Γ)
erase-expr (new C x) = AST.new C (List.erase erase-expr x)
erase-expr unit = AST.unit
erase-expr null = AST.null
erase-expr (num x) = AST.num x
erase-expr (iop x e e₁) = AST.iop x (erase-expr e) (erase-expr e₁)
erase-expr (call e m x) = AST.call (erase-expr e) m (List.erase erase-expr x)
erase-expr (var x) = AST.var (index x)
erase-expr (get e f) = AST.get (erase-expr e) f
erase-expr (upcast s e) = erase-expr e

mutual
  erase-stmt : ∀ {I r O} → Stmt I r O → AST.Stmt (length I) (length O)
  erase-stmt (loc a) = AST.loc a
  erase-stmt (asgn x e) = AST.asgn (index x) (erase-expr e)
  erase-stmt (set x f e) = AST.set (erase-expr x) f (erase-expr e)
  erase-stmt (do x) = AST.do (erase-expr x)
  erase-stmt (ret x) = AST.ret (erase-expr x)
  erase-stmt raise = AST.raise
  erase-stmt (try s catch s₁) = AST.try erase-stmt s catch erase-stmt s₁
  erase-stmt (while x do s) = AST.while erase-expr x do erase-stmt s
  erase-stmt (block x) = AST.block (erase-stmts x)

  -- this is an instance of Star.gmap, but the higher order version
  -- fails to pass the termination checker
  erase-stmts : ∀ {I r O} → Stmts I r O → AST.Stmts (length I) (length O)
  erase-stmts ε = ε
  erase-stmts (x ◅ st) = erase-stmt x ◅ erase-stmts st

erase-body : ∀ {I a} → Body I a → AST.Body (length I)
erase-body (body s* e) = AST.body (erase-stmts s*) (erase-expr e)

erase-constructor : ∀ {cid} → Constructor cid → AST.Constructor (length (Class.constr (Σ cid)))
erase-constructor (super args then b) = AST.super (List.erase erase-expr args) then (erase-body b)
erase-constructor (body x) = AST.body (erase-body x)

erase-method : ∀ {cid m as b} → Method cid m (as , b) → AST.Method (length as)
erase-method (super _ ⟨ args ⟩then b) = AST.super⟨ List.erase erase-expr args ⟩then (erase-body b)
erase-method (body x) = AST.body (erase-body x)

erase-implementation : ∀ {cid} → Implementation cid → AST.Implementation cid
erase-implementation (implementation construct mbodies) =
  AST.implementation (erase-constructor construct) (map-all erase-method mbodies)

erase-prog : ∀ {a} → Prog a → AST.Prog
erase-prog (ℂ , b) = (λ cid → erase-implementation (ℂ cid)) , erase-body b
