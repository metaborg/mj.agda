import MJ.Classtable

import MJ.Syntax.Untyped as Syntax
import MJ.Classtable.Core as Core

module MJ.Semantics.Smallstep {c} (Ct : Core.Classtable c)(ℂ : Syntax.Classes Ct) where

open import Prelude

open import Data.Vec as V hiding (init; _>>=_; _∈_; _[_]=_)
open import Data.Vec.All.Properties.Extra as Vec∀++
open import Data.Sum
open import Data.String
open import Data.List.Most as List
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Relation.Nullary.Decidable
open import Data.Star hiding (return; _>>=_)

import Data.Vec.All as Vec∀

open Syntax Ct
open Core c
open Classtable Ct
open import MJ.Classtable.Membership Ct

open import MJ.Types

{-}
-- fragment of a typed smallstep semantics;
-- this is tedious, because there are so many indices to repeat and keep track of

readvar : ∀ {W Γ a} → Var Γ a → Env Γ W → Store W → Val W a
readvar v E μ = {!!}

data Cont (Γ : Ctx) : Ty c → Ty c → Set where
  k-iopₗ : ∀ {a} → NativeBinOp → Cont int a → Expr Γ

data State : Ty c → Set where
  exp  : ∀ {Γ W a b} → Store W → Env Γ W → Expr Γ a → Cont a b → State b
  skip : ∀ {Γ W a b} → Store W → Env Γ W → Val W a → Cont a b → State b

data _⟶_ {b} : State b → State b → Set where

  exp-var : ∀ {W Γ a}{μ : Store W}{E : Env Γ W}{x k} →
    exp μ E (var {a = a} x) k ⟶ skip μ E (readvar x E μ) k

  iopₗ     : ∀ {W Γ a}{μ : Store W}{E : Env Γ W}{x k l r f} →
    exp μ E (iop f l r) k ⟶ k-iopₗ 
-}

Loc = ℕ

data Val : Set where
  num  : ℕ → Val
  unit : Val
  null : Val
  ref  : Cid c → Loc → Val

default : Ty c → Val
default a = {!!}

data StoreVal : Set where
  val  : Val → StoreVal

Env : ℕ → Set
Env = Vec Val

Store = List StoreVal

data Focus (n : ℕ) : ℕ → Set where
  stmt : ∀ {o} → Stmt n o → Focus n o
  continue : Focus n n
  exp  : Expr n → Focus n n
  val  : Val    → Focus n n
  vals : List Val → Focus n n

data Cont (n : ℕ) : Set where
  k-done : Cont n
  k-iopₗ  : NativeBinOp → Cont n → Expr n → Cont n
  k-iopᵣ  : NativeBinOp → Val → Cont n → Cont n
  k-new  : Cid c → Cont n → Cont n
  k-args  : List Val → List (Expr n) → Cont n → Cont n
  k-get  : String → Cont n → Cont n
  k-call : String → Cont n → Cont n

  k-asgn : Fin n → Cont n → Cont n
  k-seq  : ∀ {o} → Stmts n o → Cont o → Cont n
  k-set₁ : String → Expr n → Cont n → Cont n
  k-set₂ : Val → String → Cont n → Cont n

data Config : Set where
  ⟨_,_,_,_⟩ : ∀ {n o} → Store → Env n → Focus n o → Cont o → Config

data _⟶_ : Config → Config → Set where
  ----
  -- expressions
  ----

  num : ∀ {n}{E : Env n}{μ i k} →
    ⟨ μ , E , exp (num i) , k ⟩ ⟶ ⟨ μ , E , val (num i) , k ⟩
  unit : ∀ {n}{E : Env n}{μ k} →
    ⟨ μ , E , exp unit , k ⟩ ⟶ ⟨ μ , E , val unit , k ⟩
  null : ∀ {n}{E : Env n}{μ k} →
    ⟨ μ , E , exp null , k ⟩ ⟶ ⟨ μ , E , val null , k ⟩

  var : ∀ {n}{E : Env n}{μ x k ℓ v} →
    μ [ ℓ ]= (val v) →
    ⟨ μ , E , exp (var x) , k ⟩ ⟶ ⟨ μ , E , val v , k ⟩

  iopₗ     : ∀ {n}{E : Env n}{μ k f l r} →
    ⟨ μ , E , exp (iop f l r) , k ⟩ ⟶ ⟨ μ , E , exp l , k-iopₗ f k r ⟩
  iopᵣ     : ∀ {n}{E : Env n}{μ k f v r} →
    ⟨ μ , E , val v , (k-iopₗ f k r) ⟩ ⟶ ⟨ μ , E , exp r , k-iopᵣ f v k ⟩
  iop-red : ∀ {n}{E : Env n}{μ k f vᵣ vₗ} →
    ⟨ μ , E , val (num vᵣ) , (k-iopᵣ f (num vₗ) k) ⟩ ⟶ ⟨ μ , E , val (num (f vₗ vᵣ)) , k ⟩

  new : ∀ {n}{E : Env n}{μ k cid e es} →
    ⟨ μ , E , exp (new cid (e ∷ es)), k ⟩ ⟶ ⟨ μ , E , exp e , k-args [] es (k-new cid k) ⟩
  new-nil : ∀ {n}{E : Env n}{μ k cid} →
    ⟨ μ , E , exp (new cid []), k ⟩ ⟶ ⟨ μ List.∷ʳ {!!} , E , {!!} , k ⟩
  new-red : ∀ {n}{E : Env n}{μ k cid vs} →
    ⟨ μ , E , vals vs , k-new cid k ⟩ ⟶ ⟨ μ List.∷ʳ {!!} , E , {!!} , k ⟩

  args : ∀ {n}{E : Env n}{μ k e es v vs} →
    ⟨ μ , E , val v , k-args vs (e ∷ es) k ⟩ ⟶ ⟨ μ , E , exp e , k-args (vs List.∷ʳ v) es k ⟩
  args-red : ∀ {n}{E : Env n}{μ k v vs} →
    ⟨ μ , E , val v , k-args vs [] k ⟩ ⟶ ⟨ μ , E , vals (vs List.∷ʳ v) , k ⟩

  get : ∀ {n}{E : Env n}{μ k e m} →
    ⟨ μ , E , exp (get e m) , k ⟩ ⟶ ⟨ μ , E , exp e , k-get m k ⟩
  get-red : ∀ {n}{E : Env n}{μ k c o m} →
    ⟨ μ , E , val (ref c o) , k-get m k ⟩ ⟶ ⟨ μ , E , {!!} , k ⟩

  call : ∀ {n}{E : Env n}{μ k e m args} →
    ⟨ μ , E , exp (call e m args), k ⟩ ⟶ ⟨ μ , E , exp e , k-args [] args (k-call m k) ⟩
  call-red : ∀ {n}{E : Env n}{μ k m v vs} →
    ⟨ μ , E , vals (v ∷ vs) , k-call m k ⟩ ⟶ ⟨ μ , E , {!!} , k ⟩

  ----
  -- statements
  ----

  next : ∀ {n}{E : Env n}{μ j o}{s : Stmt n j}{st : Stmts j o}{k} →
    ⟨ μ , E , continue , k-seq (s ◅ st) k ⟩ ⟶ ⟨ μ , E , stmt s , k-seq st k ⟩

  loc  : ∀ {n}{E : Env n}{μ k a} →
    ⟨ μ , E , stmt (loc a) , k ⟩ ⟶ ⟨ μ , default a ∷ E , continue , k ⟩

  asgn : ∀ {n}{E : Env n}{μ k e x} →
    ⟨ μ , E , stmt (asgn x e) , k ⟩ ⟶ ⟨ μ , E , exp e , k-asgn x k ⟩
  asgn-red : ∀ {n}{E : Env n}{μ k v x} →
    ⟨ μ , E , val v , k-asgn x k ⟩ ⟶ ⟨ μ , (E V.[ x ]≔ v) , continue , k ⟩

  set₁ : ∀ {n}{E : Env n}{μ m k e e'} →
    ⟨ μ , E , stmt (set e m e') , k ⟩ ⟶ ⟨ μ , E , exp e , k-set₁ m e' k ⟩
  set₂ : ∀ {n}{E : Env n}{μ m k v e'} →
    ⟨ μ , E , val v , k-set₁ m e' k ⟩ ⟶ ⟨ μ , E , exp e' , k-set₂ v m k ⟩
  set-red : ∀ {n}{E : Env n}{μ μ' m C k v o O} →
    maybe-lookup     o μ ≡ just O →
    maybe-write o {!!} μ ≡ just μ' →
    ⟨ μ , E , val v , k-set₂ (ref C o) m k ⟩ ⟶ ⟨ μ' , E , continue , k ⟩

-- A few useful predicates on configurations

Stuck : Config → Set
Stuck φ = ¬ ∃ λ φ' → φ ⟶ φ'

data Done : Config → Set where
  done : ∀ {n}{E : Env n}{μ v} → Done ⟨ μ , E , val v , k-done ⟩

-- reflexive, transitive-closure of step
_⟶ₖ_ : Config → Config → Set
_⟶ₖ_ = Star _⟶_
