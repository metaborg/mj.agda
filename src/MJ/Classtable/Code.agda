open import MJ.Types
import MJ.Classtable.Core as Core

module MJ.Classtable.Code {c}(Ct : Core.Classtable c) where

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
open import MJ.Syntax Ct

data Body (I : Ctx) : Ty c → Set where
  body : ∀ {r}{O : Ctx} → Stmts I r O → Expr O r → Body I r

{-
A helper to generate the shape of the context for method bodies
-}
methodctx : Cid c → List (Ty c) → Ctx
methodctx cid as = (ref cid ∷ as)

{-
A helper to generate the shape of the context for constructors
-}
constrctx : Cid c → Ctx
constrctx cid = let cl = Σ cid in (ref cid ∷ Class.constr cl)

-- A method is either just a body, or a body prefixed by a super call.
data Method (cid : Cid c)(m : String) : Sig c → Set where
  super_⟨_⟩then_ : ∀ {as b} →
                let
                  pid = Class.parent (Σ cid)
                  Γ   = methodctx cid as
                in
                  -- must have a super to call, with the same signature
                  AccMember pid METHOD m (as , b) →
                  -- super call arguments
                  All (Expr Γ) as →
                  -- body
                  Body (Γ +local b) b → Method cid m (as , b)
  body        : ∀ {as b} → Body (methodctx cid as) b → Method cid m (as , b)

-- Constructors are similar
data Constructor (cid : Cid c) : Set where
  super_then_ : let
                  pid = Class.parent (Σ cid)
                  pclass = Σ pid
                  Γ   = constrctx cid
                in
                  -- super call arguments
                  All (Expr Γ) (Class.constr pclass) →
                  -- body
                  Body Γ void →
                  Constructor cid
  body        : Body (constrctx cid) void → Constructor cid

{-
A class implementation consists of a constructor and a body for every
METHOD declaration.
-}
record Implementation (cid : Cid c) : Set where
  constructor implementation
  open Class (Σ cid) public
  field
    construct : Constructor cid
    mbodies   : All (λ{ (name , sig) → Method cid name sig }) (decls METHOD)

-- Code is a lookup table for class implementations for every class identifier
Code = ∀ cid → Implementation cid

-- Mirroring `IsMember METHOD` we define the notion of an inherited method body.
InheritedMethod : ∀ (cid : Cid c)(m : String) → Sig c → Set
InheritedMethod cid m s = ∃ λ pid → Σ ⊢ cid <: pid × Method pid m s
