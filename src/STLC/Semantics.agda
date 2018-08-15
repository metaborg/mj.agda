module STLC.Semantics where

-- This file contains the definitional interpreter for STLC described
-- in Section 2 of the paper.

open import Data.Nat
open import Data.Integer
open import Data.List.Most
open import Data.Maybe hiding (All)


------------
-- SYNTAX --
------------

-- These definitions correspond to Section 2.1, except we have
-- included numbers (integers) and integer operations in the language.

data Ty : Set where
  unit : Ty
  _⇒_  : (a b : Ty) → Ty
  int  : Ty

Ctx = List Ty

-- Below, `Expr` uses `_∈_` from `Relation.Binary` in the Agda
-- Standard Library to represent typed de Bruijn indices which witness
-- the existence of an entry in the type context.

data Expr (Γ : Ctx) : Ty → Set where
  unit  : Expr Γ unit
  var   : ∀ {t} → t ∈ Γ → Expr Γ t
  ƛ     : ∀ {a b} → Expr (a ∷ Γ) b → Expr Γ (a ⇒ b)
  _·_   : ∀ {a b} → Expr Γ (a ⇒ b) → Expr Γ a → Expr Γ b
  num   : ℤ → Expr Γ int
  iop   : (ℤ → ℤ → ℤ) → (l r : Expr Γ int) → Expr Γ int


-----------------------------
-- VALUES AND ENVIRONMENTS --
-----------------------------

-- These definitions correspond to Section 2.2.
--
-- Note that the `All` type described in Section 2.2 of the paper (for
-- simplicity) does not mention universe levels, whereas the `All`
-- definition below refers to `Data.List.All` in the Agda Standard
-- Library which is defined in a universe polymorphic manner.

mutual
  data Val : Ty → Set where
    unit  : Val unit
    ⟨_,_⟩ : ∀ {Γ a b} → Expr (a ∷ Γ) b → Env Γ → Val (a ⇒ b)
    num   : ℤ → Val int

  Env : Ctx → Set
  Env Γ = All Val Γ

-- The `lookup` function described in Section 2.2 of the paper is also
-- defined in `Data.List.All` in the Agda Standard Library.


-----------
-- MONAD --
-----------

-- These definitions correspond to Section 2.3.

M : Ctx → Set → Set
M Γ a  =  Env Γ → Maybe a

_>>=_    : ∀ {Γ a b} → M Γ a → (a → M Γ b) → M Γ b
(f >>= c) E with (f E)
... | just x = c x E
... | nothing = nothing

return   : ∀ {Γ a} → a → M Γ a
return x E = just x

getEnv   : ∀ {Γ} → M Γ (Env Γ)
getEnv E = return E E

usingEnv : ∀ {Γ Γ' a} → Env Γ → M Γ a → M Γ' a
usingEnv E f _ = f E

timeout  : ∀ {Γ a} → M Γ a
timeout = λ _ → nothing


-----------------
-- INTERPRETER --
-----------------

-- These definitions correspond to Section 2.4.

eval : ℕ → ∀ {Γ t} → Expr Γ t → M Γ (Val t)
eval zero     _           =
  timeout
eval (suc k)  unit        =
  return unit
eval (suc k)  (var x)     =
  getEnv >>= λ E →
  return (lookup-all E x)
eval (suc k)  (ƛ b)       =
  getEnv >>= λ E →
  return ⟨ b , E ⟩
eval (suc k)  (l · r)     =
  eval k l >>= λ{ ⟨ e , E ⟩ →
  eval k r >>= λ v →
  usingEnv (v ∷ E) (eval k e) }
eval (suc k)  (num x)     =
  return (num x)
eval (suc k)  (iop f l r) =
  eval k l >>= λ{ (num vₗ) →
  eval k r >>= λ{ (num vᵣ) →
  return (num (f vₗ vᵣ)) }}
