open import Agda.Primitive
open import Data.Unit
open import Data.Nat hiding (_⊔_ ; _^_)
open import Data.Integer hiding (_⊔_)
open import Data.List.Most
open import Data.Product
open import Data.Maybe hiding (All)
open import Data.List.All as List∀
open import Data.List.Any
open import Data.List.Prefix
open import Data.List.Properties.Extra
open import Data.List.All.Properties.Extra
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Relation.Unary.Weakening.ListPrefix

-- This file contains the definitional interpreter for STLC using
-- scopes and frames, described in Section 4 of the paper.

-- The scopes-and-frames library assumes that we are given a
-- particular scope graph, with `k` scopes.  The following module is
-- parameterized by a `k` representing the number of scopes that a
-- particular object language program has.

module STLCSF.Semantics where


-----------
-- TYPES --
-----------

data Ty : Set where
  unit : Ty
  _⇒_  : (a b : Ty) → Ty
  int  : Ty

-- The library is loaded and passed two arguments:
--
-- * `k` is the size of the scope graph for an object program
--
-- * `Ty` is the type of declarations in the scope graph

open import ScopesFrames.ScopeGraph (λ _ → Ty) ℕ ⊤
open Graph

-- Our interpreter is parameterized by a scope graph, via the module
-- below.

module Syntax (g : Graph) where

  -- We load all the scope graph definitions in the scope graph
  -- library, by passing the object scope graph `g` as module
  -- parameter:
  open import ScopesFrames.FrameHeap (λ _ → Ty) ℕ ⊤
  open UsesGraph {g}


  ------------
  -- SYNTAX --
  ------------

  -- We can now define our well-typed syntax as described in the paper
  -- Section 4.2:
  data Expr (s : Scope (ı g)) : Ty → Set where
    unit  : Expr s unit
    var   : ∀ {t} → (g ⊢⇣ s ↦ t) → Expr s t
    ƛ     : ∀ {s' a b} → ⦃ shape : nodeOf⇣ g s' ≡ ( [ a ] , [ s ] ) ⦄ → Expr s' b → Expr s (a ⇒ b)
    _·_   : ∀ {a b} → Expr s (a ⇒ b) → Expr s a → Expr s b
    num   : ℤ → Expr s int
    iop   : (ℤ → ℤ → ℤ) → (l r : Expr s int) → Expr s int


  ------------
  -- VALUES --
  ------------

  -- We can also define well-typed values as described in the paper
  -- Section 4.4:
  data Val : Ty → (Σ : HeapTy) → Set where
    unit   : ∀ {Σ} → Val unit Σ
    ⟨_,_⟩  : ∀ {Σ s s' a b}⦃ shape : nodeOf⇣ g s' ≡ ( [ a ] , [ s ] ) ⦄ →
             Expr s' b → Frame s Σ → Val (a ⇒ b) Σ
    num    : ∀ {Σ} → ℤ → Val int Σ

  val-weaken : ∀ {t Σ Σ'} → Σ ⊑ Σ' → Val t Σ → Val t Σ'
  val-weaken ext ⟨ e , f ⟩ = ⟨ e , wk ext f ⟩
  val-weaken ext unit      = unit
  val-weaken ext (num z)   = num z

  -- We can now load the frames definitions of the scopes-and-frames
  -- library.  As described in Section 4.3 of the paper, our notion of
  -- frame assumes a notion of weakenable value, to be passed as
  -- module arguments to `UsesVal`:
  open UsesVal Val val-weaken renaming (getFrame to getFrame')

  -- We rename `getFrame` from the scopes-and-frames library so that
  -- we can use `getFrame` as the name of the monadic operation which
  -- returns the "current frame pointer" below.


  -----------
  -- MONAD --
  -----------

  -- These definitions correspond to Section 4.4.

  M : (s : Scope (ı g)) → (HeapTy → Set) → HeapTy → Set
  M s P Σ = Frame s Σ → Heap Σ → Maybe (∃ λ Σ' → (Heap Σ' × P Σ' × Σ ⊑ Σ'))

  _>>=_       :  ∀ {s Σ}{P Q : List (Scope (ı g)) → Set} →
                 M s P Σ → (∀ {Σ'} → P Σ' → M s Q Σ') → M s Q Σ
  (a >>= b) f h
    with (a f h)
  ...  | nothing = nothing
  ...  | just (Σ , h' , v , ext)
       with (b v (wk ext f) h')
  ...     | nothing = nothing
  ...     | just (Σ' , h'' , v' , ext') = just (Σ' , h'' , v' , ext ⊚ ext')

  return      :  ∀ {s Σ}{P : List (Scope (ı g)) → Set} → P Σ → M s P Σ
  return v f h = just (_ , h , v , ⊑-refl)

  getFrame    :  ∀ {s Σ} → M s (Frame s) Σ
  getFrame f = return f f

  usingFrame  :  ∀ {s s' Σ}{P : List (Scope (ı g)) → Set} → Frame s Σ → M s P Σ → M s' P Σ
  usingFrame f a _ = a f

  timeout     :  ∀ {s Σ}{P : List (Scope (ı g)) → Set} → M s P Σ
  timeout _ _ = nothing

  init        :  ∀ {Σ s' ds es}(s : Scope (ı g))⦃ shape : nodeOf⇣ g s ≡ (ds , es) ⦄ →
                 Slots ds Σ → Links es Σ → M s' (Frame s) Σ
  init {Σ} s slots links _ h
    with (initFrame s slots links h)
  ...  | (f' , h') = just (_ , h' , f' , ∷ʳ-⊒ s Σ)

  getv        :  ∀ {s t Σ} → (g ⊢⇣ s ↦ t) → M s (Val t) Σ
  getv p f h = return (getVal p f h) f h

  _^_         :  ∀ {Σ Γ}{P Q : List (Scope (ı g)) → Set} → ⦃ w : Wk Q ⦄ →
                 M Γ P Σ → Q Σ → M Γ (P ⊗ Q) Σ
  (a ^ x) f h
    with (a f h)
  ...  | nothing = nothing
  ...  | just (Σ , h' , v , ext) = just (Σ , h' , (v , wk ext x) , ext)

  sₑ : ∀ {s t} → Expr s t → Scope (ı g)
  sₑ {s} _ = s

  eval : ℕ → ∀ {s t Σ} → Expr s t → M s (Val t) Σ
  eval zero     _      =
    timeout
  eval (suc k) unit    =
    return unit
  eval (suc k) (var x) =
    getv x
  eval (suc k) (ƛ e)   =
    getFrame >>= λ f →
    return ⟨ e , f ⟩
  eval (suc k) (l · r) =
    eval k l >>= λ{ ⟨ e , f ⟩ →
    (eval k r ^ f) >>= λ{ (v , f) →
    init (sₑ e) (v ∷ []) (f ∷ []) >>= λ f' →
    usingFrame f' (eval k e) }}
  eval (suc k) (num z) =
    return (num z)
  eval (suc k) (iop f l r) =
    eval k l >>= λ{ (num z₁) →
    eval k r >>= λ{ (num z₂) →
    return (num (f z₁ z₂)) }}
