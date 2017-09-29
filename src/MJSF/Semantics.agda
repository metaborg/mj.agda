open import Data.Nat hiding (_^_ ; _+_)
open import Data.List.Most
open import Data.Integer
open import Data.Unit
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Function
open import Data.Star hiding (return ; _>>=_ ; map)

open import Common.Strength

module MJSF.Semantics (k : ℕ) where

open import MJSF.Syntax k
open import MJSF.Values k
open import MJSF.Monad k
open import ScopeGraph.ScopesFrames k Ty hiding (Scope)

module Syntax (g : Graph) where

  open ValuesG g
  open MonadG g
  open UsesVal Valᵗ valᵗ-weaken renaming (getFrame to getFrame')

  -----------------
  -- AUXILIARIES --
  -----------------
  --------------
  -- DEFAULTS --
  --------------

  default : {Σ : List Scope} → (t : VTy) → Val t Σ
  default int     = num (ℤ.pos 0)
  default (ref s) = null
  default void    = void

  default<: : {Σ : List Scope} → (t : VTy) → Val<: t Σ
  default<: t = upcast refl (default t)

  defaults : ∀ {fs : List Ty}{Σ} → All (#v (λ _ → ⊤)) fs → Slots fs Σ
  defaults {[]}          []           = []
  defaults {vᵗ t ∷ fs} (#v' _ ∷ ts) = vᵗ (reflv (default t)) ∷ defaults {fs} ts

  mutual
    eval<:  :  ℕ → ∀ {t s Σ} → Expr<: s t → M s (Val<: t) Σ
    eval    :  ℕ → ∀ {t s Σ} → Expr s t → M s (Val<: t) Σ

    eval<: k (upcast σ e) = fmap (up<: σ) (eval k e)

    -- coerces to val
    evalᶜ : ℕ → ∀ {t s Σ} → Expr<: s t → M s (Val t) Σ
    evalᶜ k e = join (fmap coerceᴹ (eval<: k e))

    eval zero _ = timeoutᴹ
    eval (suc k) (num x) = return (reflv (num x))
    eval (suc k) (iop x l r) = evalᶜ k l >>= λ{ (num il) →
                               evalᶜ k r >>= λ{ (num ir) →
                               return (reflv (num (il + ir))) }}
    eval (suc k) null = return (reflv null)
    eval (suc k) (var x)          =  getv x >>= λ{ (vᵗ v) → return v }
    eval (suc k) (new x)          =  getv x >>= λ{ (cᵗ class _ f) →
                                     usingFrame f (init-obj k class) >>= λ{ f' →
                                     return (reflv (ref f')) }}
    eval (suc k) (get e p)        =  evalᶜ k e >>= λ{ null → raise ; (ref f) →
                                     usingFrame f (getv p) >>= λ{ (vᵗ v) →
                                     return v }}
    eval (suc k) (call e p args)  =  eval<: k e >>= λ v →
                                     (coerceᴹ v ^ v) >>= λ{ (null , _) → raise ; (ref f , v) →
                                     (usingFrame f (getv p) ^ (v ′ f))
                                      >>= λ{ (mᵗ (meth s ⦃ shape ⦄ b) , v , f) →
                                     (eval-args k args ^ (v ′ f)) >>= λ{ (slots , v , f) →
                                     init s ⦃ shape ⦄ (vᵗ v ∷ slots) (f ∷ []) >>= λ f' →
                                     usingFrame f' (eval-body k b) }}}
  
    eval-args : ℕ → ∀ {s ts Σ} → All (Expr<: s) ts → M s (Slots (Data.List.Most.map vᵗ ts)) Σ
    eval-args zero _ = timeoutᴹ
    eval-args (suc k) [] = return []
    eval-args (suc k) (e ∷ es) = eval<: k e >>= λ v →
                                 (eval-args k es ^ v) >>= λ{ (slots , v) →
                                 return (vᵗ v ∷ slots) }

    eval-stmt : ℕ → ∀ {s s' Σ} → Stmt s s' → M s (Frame s') Σ
    eval-stmt zero _ = timeoutᴹ
    eval-stmt (suc k) (do e) = eval<: k e >>= λ _ → getFrame
    eval-stmt (suc k) (ifz c t e) =
      evalᶜ k c >>= λ{ (num (+ zero)) → eval-stmt k t
      ; (num i) → eval-stmt k e }
    eval-stmt (suc k) (set e x e') =
      evalᶜ k e >>= λ{ null → raise ; (ref f) →
      (eval<: k e' ^ f) >>= λ{ (v , f) →
      usingFrame f (setv x (vᵗ v)) >>= λ _ → getFrame }}
    eval-stmt (suc k) (loc s t) =
      getFrame >>= λ f → init s (vᵗ (default<: t) ∷ []) (f ∷ [])
    eval-stmt (suc k) (asgn x e) =
      eval<: k e >>= λ{ v →
      setv x (vᵗ v) >>= λ _ → getFrame }
    eval-stmt (suc k) (block stmts) =
      getFrame >>= λ f →
      (eval-stmts k stmts ^ f) >>= λ{ (_ , f) →
      return f }

    eval-stmts : ℕ → ∀ {s s' Σ} → Stmts s s' → M s (Frame s') Σ
    eval-stmts zero _ = timeoutᴹ
    eval-stmts (suc k) ε = getFrame
    eval-stmts (suc k) (stmt ◅ stmts) = eval-stmt k stmt >>= λ f' →
                                        usingFrame f' (eval-stmts k stmts)

    eval-body : ℕ → ∀ {s t Σ} → Body s t → M s (Val<: t) Σ
    eval-body zero _ = timeoutᴹ
    eval-body (suc k) (body stmts e) = eval-stmts k stmts >>= λ f →
                                       usingFrame f (eval<: k e)
    eval-body (suc k) (body-void stmts) = eval-stmts k stmts >>= λ f →
                                          return (reflv void)

    init-obj : ℕ → ∀ {sʳ s Σ} → Class sʳ s → M sʳ (Frame s) Σ
    init-obj zero _ = timeoutᴹ
    init-obj (suc k) (class0 ⦃ shape ⦄ ms fs oms)
      = getFrame >>= λ f →
        init _ ⦃ shape ⦄ (slotify ms ++-all defaults fs) (f ∷ []) >>= λ f' →
        (usingFrame f' (override oms) ^ f') >>= λ{ (_ , f') → return f' }
    init-obj (suc k) (class1 p ⦃ shape ⦄ ms fs oms)
      = getv p >>= λ{ (cᵗ class' _ f') →
        (usingFrame f' (init-obj k class') ^ f') >>= λ{ (f , f') →
        init _ ⦃ shape ⦄ (slotify ms ++-all defaults fs) (f' ∷ f ∷ []) >>= λ f'' →
        (usingFrame f'' (override oms) ^ f'') >>= λ{ (_ , f'') → return f'' }}}

    slotify : ∀ {ms s Σ} → All (#m (Meth s)) ms → Slots ms Σ
    slotify {[]}            []           = []
    slotify {mᵗ ts rt ∷ mts} (#m' m ∷ ms) = mᵗ m ∷ slotify {mts} ms
    
    override : ∀ {s Σ}{oms : List (List VTy × VTy)} → 
               All (λ x → (s ↦ (mᵗ (proj₁ x) (proj₂ x))) × Meth s (proj₁ x) (proj₂ x)) oms →
               M s (λ _ → ⊤) Σ
    override [] = return tt
    override ((p , m) ∷ oms) = setv p (mᵗ m) >>= λ _ →
                               override oms

