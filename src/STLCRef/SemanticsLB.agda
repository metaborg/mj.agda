module STLCRef.SemanticsLB where

-- This file contains a definitional interpreter for STLC+Ref as
-- described in Section 3 of the paper.  The interpreter operates with
-- the notion of monadic bind described in Section 3.3 of the paper;
-- see `Semantics.agda` for the version of the interpreter of STLC+Ref
-- using monadic strength as described in Section 3.4 of the paper.

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
open import Common.Weakening

------------
-- SYNTAX --
------------

-- These definitions correspond to Section 3.1, except we have
-- included integers, integer operations, and a simple conditional
-- expression (if-zero) in the language.

data Ty : Set

Ctx = List Ty

data Ty where
  _⇒_  : (a b : Ty) → Ty
  unit : Ty
  int  : Ty
  ref  : Ty -> Ty

data Expr (Γ : List Ty) : Ty → Set where
  unit  : Expr Γ unit
  var   : ∀ {t} → t ∈ Γ → Expr Γ t
  ƛ     : ∀ {a b} → Expr (a ∷ Γ) b → Expr Γ (a ⇒ b)
  _·_   : ∀ {a b} → Expr Γ (a ⇒ b) → Expr Γ a → Expr Γ b
  num   : ℤ → Expr Γ int
  iop   : (ℤ → ℤ → ℤ) → (l r : Expr Γ int) → Expr Γ int
  ifz   : ∀ {t} → Expr Γ int → Expr Γ t → Expr Γ t → Expr Γ t
  ref   : ∀ {t} → Expr Γ t → Expr Γ (ref t)
  !_    : ∀ {t} → Expr Γ (ref t) → Expr Γ t
  _≔_   : ∀ {t} → Expr Γ (ref t) → Expr Γ t → Expr Γ unit


-----------------------
-- STORES AND VALUES --
-----------------------

StoreTy = List Ty

-- `Val` uses `_∈_` from `Relation.Binary` in the Agda Standard
-- Library to represent typed locations which witness the existence of
-- a store location in the store type.

mutual
  data Val : Ty → (Σ : StoreTy) → Set where
    loc    : ∀ {Σ t} → t ∈ Σ → Val (ref t) Σ
    unit   : ∀ {Σ} → Val unit Σ
    ⟨_,_⟩  : ∀ {Σ Γ a b} → Expr (a ∷ Γ) b → Env Γ Σ → Val (a ⇒ b) Σ
    num   : ∀ {Σ} → ℤ → Val int Σ

  Env : (Γ : Ctx)(Σ : StoreTy) → Set
  Env Γ Σ = All (λ t → Val t Σ) Γ

Store : (Σ : StoreTy) → Set
Store Σ = All (λ t → Val t Σ) Σ

-- The `lookup-store` function is defined in terms of the `lookup`
-- function from `Data.List.All` in the Agda Standard Library.
lookup-store : ∀ {Σ t} → t ∈ Σ → Store Σ → Val t Σ
lookup-store x μ = lookup μ x

-- The `update-store` function is defined in terms of the update
-- function for the `All` type: `_All[_]≔'_` from the Standard Library
-- extension (contained in the `lib/*` folder of this artifact).
update-store : ∀ {Σ t} → t ∈ Σ → Val t Σ → Store Σ → Store Σ
update-store ptr v μ = μ All[ ptr ]≔' v


-----------
-- MONAD --
-----------

-- These definitions correspond to Section 3.3.

M : ∀ {i}(Γ : Ctx) → (p : StoreTy → Set i) → (Σ : StoreTy) → Set i
M Γ p Σ = Env Γ Σ → Store Σ → Maybe (∃ λ Σ' → Store Σ' × p Σ' × Σ ⊑ Σ')

mutual
  weaken-val  : ∀ {a}{Σ Σ' : StoreTy} → Σ ⊑ Σ' → Val a Σ → Val a Σ'
  weaken-val ext unit      = unit
  weaken-val ext (loc l)   = loc (∈-⊒ l ext)
  weaken-val ext ⟨ e , E ⟩ = ⟨ e , weaken-env ext E ⟩
  weaken-val ext (num z)   = num z

  weaken-env  : ∀ {Γ}{Σ Σ' : StoreTy} → Σ ⊑ Σ' → Env Γ Σ → Env Γ Σ'
  weaken-env ext (v ∷ vs)  = weaken-val ext v ∷ weaken-env ext vs
  weaken-env ext []        = []

return   :    ∀ {Σ Γ}{p : List Ty → Set} → p Σ → M Γ p Σ
return x E μ = just (_ , μ , x , ⊑-refl)

_>>=_ : ∀ {Σ Γ}{p q : StoreTy → Set} →
        (f : M Γ p Σ) → (g : ∀ {Σ'} → Σ ⊑ Σ' → p Σ' → M Γ q Σ') → M Γ q Σ
(f >>= c) E μ = case (f E μ) of λ{
  nothing → nothing ;
  (just (_ , μ' , x , ext)) → case (c ext x (weaken-env ext E) μ') of λ{
    nothing → nothing ;
    (just (_ , μ'' , y , ext')) → just (_ , μ'' , y , ext ⊚ ext')
  }}

getEnv  : ∀ {Σ Γ} → M Γ (Env Γ) Σ
getEnv E = return E E

usingEnv : ∀ {Σ Γ Γ'}{p : List Ty → Set} → Env Γ Σ → M Γ p Σ → M Γ' p Σ
usingEnv E f  _ = f E

timeout : ∀ {Σ Γ}{p : List Ty → Set} → M Γ p Σ
timeout _ _ = nothing

store : ∀ {Σ t Γ} → Val t Σ → M Γ (Val (ref t)) Σ
store {Σ} {t} v _ μ
  = let ext = ∷ʳ-⊒ t Σ
        v'  = loc (∈-∷ʳ Σ t)
        μ'  = (List∀.map (weaken-val ext) μ) all-∷ʳ (weaken-val ext v)
    in just (_ , μ' , v' , ext)

deref : ∀ {Σ Γ t} → t ∈ Σ → M Γ (Val t) Σ
deref x E μ = return (lookup μ x) E μ

update : ∀ {Σ Γ t} → t ∈ Σ → Val t Σ → M Γ (λ _ → ⊤) Σ
update x v E μ = return tt E (update-store x v μ)

eval : ℕ → ∀ {Σ Γ t} → Expr Γ t → M Γ (Val t) Σ
eval zero    _           =
  timeout
eval (suc k) unit        =
  return unit
eval (suc k) (var x)     =
  getEnv >>= λ _ E →
  return (lookup E x)
eval (suc k) (ƛ e)       =
  getEnv >>= λ _ E →
  return ⟨ e , E ⟩
eval (suc k) (l · r)     =
  eval k l >>= λ{ ext ⟨ e , E ⟩ →
  eval k r >>= λ ext' v →
  usingEnv (v ∷ weaken-env ext' E) (eval k e) }  -- explicit weakening
eval (suc k) (num x)     =
  return (num x)
eval (suc k) (iop f l r) =
  eval k l >>= λ{ _ (num v) →
  eval k r >>= λ{ _ (num vᵣ) →
  return (num (f v vᵣ)) }}
eval (suc k) (ifz c t e) =
  eval k c >>= λ{ _ (num z) →
  case z of λ{ (+ zero) →
    eval k t
  ; _ →
    eval k e }}
eval (suc k) (ref e)     =
  eval k e >>= λ _ v →
  store v
eval (suc k) (! e)       =
  eval k e >>= λ{ _ (loc l) →
  deref l }
eval (suc k) (r ≔ e)     =
  eval k r >>= λ{ _ (loc l) →
  eval k e >>= λ ext v →
  update (∈-⊒ l ext) v >>= λ _ _ →             -- explicit weakening
  return unit }
