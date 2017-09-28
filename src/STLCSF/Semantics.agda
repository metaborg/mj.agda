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
open import Common.Weakening
open import Common.Strength

open Weakenable ⦃...⦄

module STLCSF.Semantics (k : ℕ) where

-- configuration of scope graphs library

data Namespace : Set where
  val    : Namespace

data Ty : Set where
  Unit : Ty
  _⇒_  : (a b : Ty) → Ty

open import ScopeGraph.ScopesFrames k Ty

module Syntax (g : Graph) where

  open UsesGraph g

  data Expr (s : Scope) : Ty → Set where
    var   : ∀ {t} → (s ↦ t) → Expr s t
    ƛ     : ∀ {s' a b} → ⦃ shape : g s' ≡ ( [ a ] , [ s ] ) ⦄ → Expr s' b → Expr s (a ⇒ b)
    _·_   : ∀ {a b} → Expr s (a ⇒ b) → Expr s a → Expr s b
    unit  : Expr s Unit

  data Val : Ty → (Σ : HeapTy) → Set where
    ⟨_,_⟩  :  ∀ {Σ s s' a b}⦃ shape : g s' ≡ ([ a ] , [ s ]) ⦄ →
              Expr s' b → Frame s Σ → Val (a ⇒ b) Σ
    unit   :  ∀ {Σ} → Val Unit Σ

  val-weaken : ∀ {t Σ Σ'} → Σ ⊑ Σ' → Val t Σ → Val t Σ'
  val-weaken ext ⟨ e , f ⟩ = ⟨ e , wk ext f ⟩
  val-weaken ext unit      = unit

  open UsesVal Val val-weaken renaming (getFrame to getFrame')

  M : (s : Scope) → (HeapTy → Set) → HeapTy → Set
  M s p Σ = Frame s Σ → Heap Σ → Maybe (∃ λ Σ' → (Heap Σ' × p Σ' × Σ ⊑ Σ'))

  _>>=_       :  ∀ {s Σ}{p q : List Scope → Set} →
                 M s p Σ → (∀ {Σ'} → p Σ' → M s q Σ') → M s q Σ
  (a >>= b) f h
    with (a f h)
  ...  | nothing = nothing
  ...  | just (Σ , h' , v , ext)
       with (b v (wk ext f) h')
  ...     | nothing = nothing
  ...     | just (Σ' , h'' , v' , ext') = just (Σ' , h'' , v' , ext ⊚ ext')

  return      :  ∀ {s Σ}{p : List Scope → Set} → p Σ → M s p Σ
  return v f h = just (_ , h , v , ⊑-refl)

  getFrame    :  ∀ {s Σ} → M s (Frame s) Σ
  getFrame f = return f f

  usingFrame  :  ∀ {s s' Σ}{p : List Scope → Set} → Frame s Σ → M s p Σ → M s' p Σ
  usingFrame f a _ = a f

  timeout     :  ∀ {s Σ}{p : List Scope → Set} → M s p Σ
  timeout _ _ = nothing

  init        :  ∀ {Σ s' ds es}(s : Scope)⦃ shape : g s ≡ (ds , es) ⦄ →
                 Slots ds Σ → Links es Σ → M s' (Frame s) Σ
  init {Σ} s slots links _ h
    with (initFrame s slots links h)
  ...  | (f' , h') = just (_ , h' , f' , ∷ʳ-⊒ s Σ)

  getv        :  ∀ {s t Σ} → (s ↦ t) → M s (Val t) Σ
  getv p f h = return (getVal p f h) f h

  _^_         :  ∀ {Σ Γ}{p q : List Scope → Set} → ⦃ w : Weakenable q ⦄ →
                 M Γ p Σ → q Σ → M Γ (p ⊗ q) Σ
  (a ^ x) f h
    with (a f h)
  ...  | nothing = nothing
  ...  | just (Σ , h' , v , ext) = just (Σ , h' , (v , wk ext x) , ext)

  sₑ : ∀ {s t} → Expr s t → Scope
  sₑ {s} _ = s

  eval : ℕ → ∀ {s t Σ} → Expr s t → M s (Val t) Σ
  eval zero     _        =  timeout
  eval (suc k) (var x)   =  getv x
  eval (suc k) (ƛ e)     =  getFrame >>= λ f → return ⟨ e , f ⟩
  eval (suc k) (l · r)   =  eval k l >>= λ{ ⟨ e , f ⟩ →
                            (eval k r ^ f) >>= λ{ (v , f) →
                            init (sₑ e) (v ∷ []) (f ∷ []) >>= λ f' →
                            usingFrame f' (eval k e) }}
  eval (suc k) unit      =  return unit
