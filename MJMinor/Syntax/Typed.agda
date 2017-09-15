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

-- subset of pure expressions
data Expr (Γ : Ctx) : Ty c → Set where
  unit     : Expr Γ void
  null     : ∀ {C} → Expr Γ (ref C)
  num      : ℕ → Expr Γ int
  var      : ∀ {a} → Var Γ a → Expr Γ a
  iop      : NativeBinOp → (l r : Expr Γ int) → Expr Γ int
  upcast   : ∀ {c c'} → Σ ⊢ c <: c' → Expr Γ (ref c) → Expr Γ (ref c')

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
  get        : ∀ {cid} → Expr Γ (ref cid) → ∀ f {ty}{acc : AccMember cid FIELD f ty} → Cmd Γ r ty
  asgn       : ∀ {a} → Var Γ a → Expr Γ a → Cmd Γ r void
  set        : ∀ {C} → Expr Γ (ref C) → ∀ f {a}{acc : AccMember C FIELD f a} → Expr Γ a → Cmd Γ r void
  raise      : Exception Γ r → Cmd Γ r void

infixl 50 _◅_
infixr 30 _◅◅_
data Block (I : Ctx)(r : Ty c): Ty c → Set where
  •⟨_⟩ : ∀ {a} → Expr I a → Block I r a
  _◅_  : ∀ {a b} → Cmd I r a → Block (a ∷ I) r b → Block I r b
  try_catch_ : ∀ {a b} → Block I r a → Block I r b → Block I r void
  while_do_  : ∀ {a b} → Block I r a → Block I r b → Block I r void

postulate _◅◅_ : ∀ {I r a b} → Block I r a → Block (a ∷ I) r b → Block I r b
postulate seq : ∀ {I r a b} → Block I r a → Block I r b → Block I r b

import MJ.Syntax Ct as MJ

defaultₑ : ∀ {Γ} a → Expr Γ a
defaultₑ void = unit
defaultₑ int = num 0
defaultₑ (ref x) = null

postulate wk : ∀ {x I r a} → Block I r a → Block (x ∷ I) r a

-- The statement structure is just too imprecise.
-- We can recover the fact that for every (s : Stmt I r O)
-- we have O ≡ a ∷ I or O ≡ I
binder? : ∀ {Γ a Γ'} → MJ.Stmt Γ a Γ' → Γ' ≡ Γ ⊎ ∃ λ a → Γ' ≡ a ∷ Γ
binder? (MJ.loc a) = inj₂ (a , refl)
binder? (MJ.asgn x x₁) = inj₁ refl
binder? (MJ.set x f x₁) = inj₁ refl
binder? (MJ.do x) = inj₁ refl
binder? (MJ.ret x) = inj₁ refl
binder? MJ.raise = inj₁ refl
binder? (MJ.try p catch p₁) = inj₁ refl
binder? (MJ.while x do p) = inj₁ refl
binder? (MJ.block x) = inj₁ refl

⟦_⟧ₑ : ∀ {Γ r a} → MJ.Expr Γ a → Block Γ r a
⟦ MJ.unit ⟧ₑ = •⟨ unit ⟩
⟦ MJ.null ⟧ₑ = •⟨ null ⟩
⟦ MJ.num x ⟧ₑ = •⟨ num x ⟩
⟦ MJ.var x ⟧ₑ = •⟨ var x ⟩
⟦ MJ.iop x e₁ e₂ ⟧ₑ = ⟦ e₁ ⟧ₑ ◅◅ wk ⟦ e₂ ⟧ₑ ◅◅ •⟨ iop x (var (here refl)) (var (here refl)) ⟩
⟦ MJ.upcast x e ⟧ₑ = {!!}
⟦ MJ.new C x ⟧ₑ = {!!}
⟦ MJ.call e m x ⟧ₑ = {!!}
⟦ MJ.get e f ⟧ₑ = {!!}

import Data.Star as *

⟦_⟧  : ∀ {I O r} → MJ.Stmt I r O → Block I r void
⟦_⟧⋆ : ∀ {I O r} → MJ.Stmts I r O → Block I r void

⟦ MJ.loc a ⟧ = val (defaultₑ a) ◅ •⟨ unit ⟩
⟦ MJ.asgn {a = a} v e ⟧ = ⟦ e ⟧ₑ ◅◅ (asgn (there v) (var $ here refl) ◅ •⟨ unit ⟩)
⟦ MJ.set r f {_}{p} e ⟧ =
    ⟦ r ⟧ₑ
  ◅◅ wk ⟦ e ⟧ₑ
  ◅◅ set (var $ there (here refl)) f {_}{p} (var $ here refl) ◅ •⟨ unit ⟩
⟦ MJ.do e ⟧  = ⟦ e ⟧ₑ ◅◅ •⟨ unit ⟩
⟦ MJ.ret e ⟧  = ⟦ e ⟧ₑ ◅◅ raise (ret $ var $ here refl) ◅ •⟨ unit ⟩
⟦ MJ.raise ⟧  = raise unchecked ◅ •⟨ unit ⟩
⟦ (MJ.try s₁ catch s₂) ⟧ = try ⟦ s₁ ⟧ catch ⟦ s₂ ⟧
⟦ (MJ.while e do s) ⟧ = while ⟦ e ⟧ₑ do ⟦ s ⟧
⟦ MJ.block s ⟧ = ⟦ s ⟧⋆

⟦ *.ε ⟧⋆ = •⟨ unit ⟩
⟦ x *.◅ st ⟧⋆ with binder? x
... | inj₁ refl = seq ⟦ x ⟧ ⟦ st ⟧⋆
⟦ MJ.loc .a *.◅ st ⟧⋆ | inj₂ (a , refl) = val (defaultₑ a) ◅ ⟦ st ⟧⋆
