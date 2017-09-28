open import Data.Nat
open import Data.List.Most
open import Data.Integer
open import Data.Product

module MJSF.Values (k : ℕ) where

open import MJSF.Syntax k
open import ScopeGraph.ScopesFrames k Ty hiding (Scope)

module ValuesG (g : Graph) where

  open SyntaxG g public
  open UsesGraph g public
  open import Common.Weakening
  open Weakenable ⦃...⦄

  ------------
  -- VALUES --
  ------------

  data Val : VTy → List Scope → Set where
    ref    :  ∀ {s Σ} → Frame s Σ → Val (ref s) Σ
    null   :  ∀ {s Σ} → Val (ref s) Σ
    num    :  ∀ {Σ} → ℤ → Val int Σ
    void   :  ∀ {Σ} → Val void Σ

  data Val<: (t : VTy) (Σ : List Scope) : Set where
    upcast  :  ∀ {t'} → (t' <: t) → Val t' Σ → Val<: t Σ

  reflv : ∀ {t Σ} → Val t Σ → Val<: t Σ
  reflv v = upcast refl v

  data Valᵗ : Ty → List Scope → Set where
    cᵗ : ∀ {sʳ s s' Σ} → Class sʳ s → Inherits s s' → Frame sʳ Σ → Valᵗ (cᵗ sʳ s) Σ
    mᵗ : ∀ {s ts rt Σ} → Meth s ts rt → Valᵗ (mᵗ ts rt) Σ
    vᵗ : ∀ {t Σ} → Val<: t Σ → Valᵗ (vᵗ t) Σ


  ---------------
  -- WEAKENING --
  ---------------

  val-weaken    :  ∀ {t Σ Σ'} → Σ ⊑ Σ' → Val t Σ → Val t Σ'
  val-weaken ext (num i)  =  num i
  val-weaken ext (ref f)  =  ref (wk ext f)
  val-weaken ext null     =  null
  val-weaken ext void     =  void

  val<:-weaken  :  ∀ {t Σ Σ'} → Σ ⊑ Σ' → Val<: t Σ → Val<: t Σ'
  val<:-weaken ext (upcast σ v)  =  upcast σ (val-weaken ext v)

  instance
    val<:-weakenable : ∀ {t} → Weakenable (Val<: t)
    val<:-weakenable = record { wk = val<:-weaken }

  valᵗ-weaken : ∀ {t Σ Σ'} → Σ ⊑ Σ' → Valᵗ t Σ → Valᵗ t Σ'
  valᵗ-weaken ext (vᵗ v)    =  vᵗ (val<:-weaken ext v)
  valᵗ-weaken ext (mᵗ m)    =  mᵗ m
  valᵗ-weaken ext (cᵗ c ic f)  =  cᵗ c ic (wk ext f)


  open UsesVal Valᵗ valᵗ-weaken renaming (getFrame to getFrame')

  
  ----------------------------
  -- UPCASTING AND COERCION --
  ----------------------------

  up<: : ∀ {t t' Σ} → t <: t' → Val<: t Σ → Val<: t' Σ
  up<: σ (upcast σ' v) = upcast (<:-trans σ' σ) v

  coerce<: : ∀ {t t' Σ} → t <: t' → Val t Σ → Heap Σ → Val t' Σ
  coerce<: refl v h = v
  coerce<: (super edge σ) null h = coerce<: σ null h
  coerce<: (super edge σ) (ref f) h
    with (lookup h f)
  ...  | (_ , links)  =  coerce<: σ (ref (lookup links edge)) h

  coerce : ∀ {t Σ} → Val<: t Σ → Heap Σ → Val t Σ
  coerce (upcast σ v) h  =  coerce<: σ v h

