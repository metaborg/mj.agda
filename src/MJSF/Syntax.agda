open import Data.Nat
open import Data.Fin using (Fin; #_; suc; zero)
open import Data.List.Most
open import Data.Integer hiding (suc)
open import Data.Product hiding (map)
open import Data.Unit
open import Data.Star hiding (return ; _>>=_ ; map)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Data.Empty

module MJSF.Syntax (k : ℕ) where

private
  Scope : Set
  Scope = Fin k

data VTy : Set where
  void : VTy
  int : VTy
  ref : Scope → VTy

data Ty : Set where
  vᵗ : VTy → Ty
  mᵗ : List VTy → VTy → Ty
  cᵗ : Scope → Scope → Ty

-------------
-- HAS TAG --
-------------

-- predicates for distinguishing tags (used for saying that a
-- particular list of declarations contain *only* declarations of a
-- particular tag).

data #v : (VTy → Set) → Ty → Set where
  #v' : ∀ {t p} → p t → #v p (vᵗ t)

data #m : (List VTy → VTy → Set) → Ty → Set where
  #m' : ∀ {ts rt p} → p ts rt → #m p (mᵗ ts rt)

data #c (sʳ : Scope) (p : Scope → Set) : Ty → Set where
  #c' : ∀ {s} → p s → #c sʳ p (cᵗ sʳ s)

open import ScopeGraph.ScopesFrames k Ty hiding (Scope)

module SyntaxG (g : Graph) where

  open UsesGraph g


  -------------------------------
  -- SUBTYPING AND INHERITANCE --
  -------------------------------

  data _<:_ : VTy → VTy → Set where
    refl   :  ∀ {t} → t <: t
    super  :  ∀ {s1 s2 t} →
              s2 ∈ edgesOf s1 → (ref s2) <: t → (ref s1) <: t

  <:-trans : ∀{t1 t2 t3} → t1 <: t2 → t2 <: t3 → t1 <: t3
  <:-trans refl           p = p
  <:-trans (super edge p) q = super edge (<:-trans p q)

  -- Inheritance links
  data Inherits : Scope → Scope → Set where
    obj   : ∀ s {ds sʳ} ⦃ shape : g s ≡ (ds , [ sʳ ]) ⦄ → Inherits s s
    super : ∀ {s ds sʳ sᵖ s'} ⦃ shape : g s ≡ (ds , sʳ ∷ sᵖ ∷ []) ⦄ → Inherits sᵖ s' → Inherits s s'


  ------------
  -- SYNTAX --
  ------------

  mutual
    data Expr (s : Scope) : VTy → Set where
      call     :  ∀ {s' ts t} → Expr s (ref s') →
                  (s' ↦ (mᵗ ts t)) →
                  All (Expr s) ts → Expr s t
      get      :  ∀ {s' t} → Expr s (ref s') → (s' ↦ vᵗ t) → Expr s t
      var      :  ∀ {t} → (s ↦ vᵗ t) → Expr s t
      new      :  ∀ {sʳ s'} → s ↦ cᵗ sʳ s' → Expr s (ref s')
      null     :  ∀ {s'} → Expr s (ref s')
      num      :  ℤ → Expr s int
      iop      :  (ℤ → ℤ → ℤ) → (l r : Expr s int) → Expr s int
      upcast   :  ∀ {t' t} → t' <: t → Expr s t' → Expr s t
      this     :  ∀ {s' self} → s ⟶ s' → self ∈ edgesOf s' →
                  Expr s (ref self)

  mutual
    data Stmt (s : Scope)(r : VTy) : Scope → Set where
      do    : ∀ {t'} → Expr s t' → Stmt s r s
      ifz   : ∀ {s' s'' : Scope} → Expr s int → Stmt s r s → Stmt s r s → Stmt s r s -- branches are blocks
      set   : ∀ {s' t'} → Expr s (ref s') → (s' ↦ vᵗ t') → Expr s t' → Stmt s r s
      loc   : ∀ (s' : Scope)(t' : VTy)⦃ shape : g s' ≡ ([ vᵗ t' ] , [ s ]) ⦄ → Stmt s r s'
      asgn  : ∀ {t'} → (s ↦ vᵗ t') → Expr s t' → Stmt s r s
      ret   : Expr s r → Stmt s r s
      block : ∀ {s'} → Stmts s r s' → Stmt s r s

    Stmts : Scope → VTy → Scope → Set
    Stmts s r s' = Star (λ s s' → Stmt s r s') s s'

  data Body (s : Scope) : VTy → Set where
    body      : ∀ {s' t} → Stmts s t s' → Expr s' t → Body s t
    body-void : ∀ {s'} → Stmts s void s' → Body s void

  data Meth (s : Scope) : List VTy → VTy → Set where
    meth  :  ∀ {ts rt}(s' : Scope)
             ⦃ shape : g s' ≡ (map vᵗ ts , [ s ]) ⦄ →
             Body s' rt →
             Meth s ts rt

  data Class (sʳ s : Scope) : Set where
    class1  :  ∀ {ms fs sᵖ}{oms : List (List VTy × VTy)} →
               sʳ ↦ (cᵗ sʳ sᵖ) →
               ⦃ shape  :  g s  ≡  (ms ++ fs ,  sʳ ∷ sᵖ ∷ []) ⦄ →
               All (#m (Meth s)) ms →
               All (#v (λ _ → ⊤)) fs →
               All (λ{ (ts , rt) → (s ↦ (mᵗ ts rt)) × Meth s ts rt }) oms →
               Class sʳ s
    class0 : ∀ {ms fs}{oms : List (List VTy × VTy)} →
             ⦃ shape : g s ≡ (ms ++ fs , [ sʳ ]) ⦄ →
             All (#m (Meth s)) ms →   -- only methods
             All (#v (λ _ → ⊤)) fs →  -- only values
             All (λ{ (ts , rt) → (s ↦ (mᵗ ts rt)) × Meth s ts rt }) oms → -- overrides
             Class sʳ s

  data Program (sʳ : Scope)(a : VTy) : Set where
    program :
      ∀ cs ⦃ shape : g sʳ ≡ (cs , []) ⦄ →
        -- implementation of all the classes
        All (#c sʳ (λ s → Class sʳ s × ∃ λ s' → Inherits s s')) cs →
        -- main function
        Body sʳ a →
        Program sʳ a
