module MJ.Syntax.Scoped where

open import Prelude
open import Data.Maybe as Maybe using (Maybe; just)
open import Data.Maybe.All as MayAll
open import Data.Vec as Vec hiding (_∈_)
open import Data.Star.Indexed
open import Data.List
open import Data.List.Properties.Extra
open import Data.List.Prefix
open import Data.List.Any
open import Data.List.All as List∀ hiding (lookup)
open import Data.List.All.Properties.Extra
open import Relation.Binary.PropositionalEquality

import Data.Vec.All as Vec∀
open Membership-≡

open import MJ.Types

NativeBinOp = ℕ → ℕ → ℕ

data Expr {n : ℕ} (Γ : Ctx c n) : Ty c → Set where
  new  : (C : Fin c) → All (Expr Γ) (Class.constr (clookup C)) → Expr Γ (ref C)
  unit : Expr Γ void
  num  : ℕ → Expr Γ int
  iop  : NativeBinOp → (l r : Expr Γ int) → Expr Γ int
  call : ∀ {cid as b} →
        Expr Γ (ref cid) → Member Σ cid MTH (as , b) → All (Expr Γ) as →
        Expr Γ b
  var  : (i : Fin n) → Expr Γ (lookup i Γ)
  get  : ∀ {cid ty} → Expr Γ (ref cid) → Member Σ cid FLD ty → Expr Γ ty
  upcast : ∀ {c c'} → Σ ⊢ c <: c' → Expr Γ (ref c) → Expr Γ (ref c')

data Cmd {n}(I : Ctx c n)(r : Ty c) : ∀ {m} → (O : Ctx c m) → Set where
  loc  : ∀ a → Expr I a → Cmd I r (a ∷ I)
  asgn : ∀ (i : Fin n) → Expr I (lookup i I) → Cmd I r I
  set  : ∀ {C a} → Expr I (ref C) →
          Member Σ C FLD a → Expr I a → Cmd I r I
  do   : ∀ {a} → Expr I a → Cmd I r I
  ret  : Expr I r → Cmd I r I

Stmts : ∀ {n m}→ (Ctx c n) → Ty c → (Ctx c m) → Set
Stmts I r O = Star ℕ (λ n m (I : Ctx c n) (O : Ctx c m) → Cmd I r O) I O

data Body {n}(I : Ctx c n) : Ty c → Set where
  body : ∀ {m r}{O : Ctx c m} → Stmts I r O → Expr O r → Body I r

-- mapping of namespace typings to the type of their implementation
Def : ∀ {ns} → Fin c → typing ns c → Set
-- methods have bodies
Def {MTH} C (as , b) = Body (ref C ∷ (fromList as)) b
-- fields have initializers
Def {FLD} C a = Body (fromList (Class.constr (clookup C))) a

record Implementation (cid : Fin c) : Set where
  constructor impl
  open Class (clookup cid) public
  field
    -- mapping construct arguments to super constructor arguments
    super-args :
      Maybe.All
        (λ p → All (Expr (fromList constr)) (Class.constr (clookup p)))
        parent

    -- definitions for all local members
    defs : ∀ ns → All (Def cid) (decls ns)

-- implementation of a classtable
record Impl : Set where
  field
    bodies : ∀ (cid : Fin c) → Implementation cid

-- get member definition from a class
getDef : ∀ {ns ty}→ (cid : Fin c) → (m : Member Σ cid ns ty) → Impl → Def (proj₁ m) ty
getDef {ns = ns} cid (_ , refl , def) I with clookup cid | inspect clookup cid
... | C@(class parent constr decls) | [ refl ] with Impl.bodies I cid
... | impl _ defs = ∈-all def (defs ns)
getDef cid (P' , super {pid = pid} p P<:P' , def) I = getDef pid (P' , P<:P' , def) I

Prog : Ty c → Set
Prog a = Impl × (Body [] a)
