module STLC.Semantics where

open import Data.Nat
open import Data.Integer
open import Data.List.Most
open import Data.Maybe hiding (All)


data Ty : Set where
  unit : Ty
  _⇒_  : (a b : Ty) → Ty
  int  : Ty

Ctx = List Ty

data Expr (Γ : Ctx) : Ty → Set where
  unit  : Expr Γ unit
  var   : ∀ {t} → t ∈ Γ → Expr Γ t
  ƛ     : ∀ {a b} → Expr (a ∷ Γ) b → Expr Γ (a ⇒ b)
  _·_   : ∀ {a b} → Expr Γ (a ⇒ b) → Expr Γ a → Expr Γ b
  num   : ℤ → Expr Γ int
  iop   : (ℤ → ℤ → ℤ) → (l r : Expr Γ int) → Expr Γ int

mutual
  data Val : Ty → Set where
    unit  : Val unit
    ⟨_,_⟩ : ∀ {Γ a b} → Expr (a ∷ Γ) b → Env Γ → Val (a ⇒ b)
    num   : ℤ → Val int

  Env : Ctx → Set
  Env Γ = All Val Γ

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

eval : ℕ → ∀ {Γ t} → Expr Γ t → M Γ (Val t)
eval zero     _        =   timeout
eval (suc k)  unit     =  return unit
eval (suc k)  (num x)  =  return (num x)
eval (suc k)  (var x)  =  getEnv >>= λ E → return (lookup E x)
eval (suc k)  (ƛ b)    =  getEnv >>= λ E → return ⟨ b , E ⟩
eval (suc k)  (l · r)  =  eval k l >>= λ{ ⟨ e , E ⟩ →
                          eval k r >>= λ v →
                          usingEnv (v ∷ E) (eval k e) }
eval (suc k) (iop f l r) =
  eval k l >>= λ{ (num vₗ) →
  eval k r >>= λ{ (num vᵣ) →
  return (num (f vₗ vᵣ)) }}
