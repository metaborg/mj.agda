module STLCRef.Semantics where

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
open import Common.Strength

data Ty : Set

Ctx = List Ty

data Ty where
  _⇒_  : (a b : Ty) → Ty
  unit : Ty
  ref  : Ty -> Ty

StoreTy = List Ty

data Expr (Γ : List Ty) : Ty → Set where
  var   : ∀ {t} → t ∈ Γ → Expr Γ t
  ƛ     : ∀ {a b} → Expr (a ∷ Γ) b → Expr Γ (a ⇒ b)
  _·_   : ∀ {a b} → Expr Γ (a ⇒ b) → Expr Γ a → Expr Γ b
  unit  : Expr Γ unit
  ref   : ∀ {t} → Expr Γ t → Expr Γ (ref t)
  !_    : ∀ {t} → Expr Γ (ref t) → Expr Γ t
  _≔_   : ∀ {t} → Expr Γ (ref t) → Expr Γ t → Expr Γ unit

mutual
  Env : (Γ : Ctx)(Σ : StoreTy) → Set
  Env Γ Σ = All (λ t → Val t Σ) Γ

  data Val : Ty → (Σ : StoreTy) → Set where
    loc    : ∀ {Σ t} → t ∈ Σ → Val (ref t) Σ
    unit   : ∀ {Σ} → Val unit Σ
    ⟨_,_⟩  : ∀ {Σ Γ a b} → Expr (a ∷ Γ) b → Env Γ Σ → Val (a ⇒ b) Σ

Store : (Σ : StoreTy) → Set
Store Σ = All (λ t → Val t Σ) Σ

M : ∀ {i}(Γ : Ctx) → (p : StoreTy → Set i) → (Σ : StoreTy) → Set i
M Γ p Σ = Env Γ Σ → Store Σ → Maybe (∃ λ Σ' → Store Σ' × p Σ' × Σ ⊑ Σ')

mutual
  weaken-val  : ∀ {a}{Σ Σ' : StoreTy} → Σ ⊑ Σ' → Val a Σ → Val a Σ'
  weaken-val ext unit      = unit
  weaken-val ext (loc l)   = loc (∈-⊒ l ext)
  weaken-val ext ⟨ e , E ⟩ = ⟨ e , weaken-env ext E ⟩

  weaken-env  : ∀ {Γ}{Σ Σ' : StoreTy} → Σ ⊑ Σ' → Env Γ Σ → Env Γ Σ'
  weaken-env ext (v ∷ vs)  = weaken-val ext v ∷ weaken-env ext vs
  weaken-env ext []        = []

instance
  weaken-val' : ∀ {t} → Weakenable (Val t)
  weaken-val' = record { weaken = weaken-val }

  weaken-unit : Weakenable (λ Σ → ⊤)
  weaken-unit = record { weaken = λ _ _ → tt }


return   :    ∀ {Σ Γ}{p : List Ty → Set} → p Σ → M Γ p Σ
return x E μ = just (_ , μ , x , ⊑-refl)

_>>=_ : ∀ {Σ Γ}{p q : StoreTy → Set} →
        (f : M Γ p Σ) → (g : ∀ {Σ'} → p Σ' → M Γ q Σ') → M Γ q Σ
(f >>= c) E μ = case (f E μ) of λ{
  nothing → nothing ;
  (just (_ , μ' , x , ext)) → case (c x (weaken-env ext E) μ') of λ{
    nothing → nothing ;
    (just (_ , μ'' , y , ext')) → just (_ , μ'' , y , ext ⊚ ext')
  }}

getEnv   :    ∀ {Σ Γ} → M Γ (Env Γ) Σ
getEnv E = return E E

setEnv   :    ∀ {Σ Γ Γ'}{p : List Ty → Set} → Env Γ Σ → M Γ p Σ → M Γ' p Σ
setEnv E f  _ = f E

timeout  :    ∀ {Σ Γ}{p : List Ty → Set} → M Γ p Σ
timeout _ _ = nothing

store    :    ∀ {Σ t Γ} → Val t Σ → M Γ (Val (ref t)) Σ
store {Σ} {t} v _ μ
  = let ext = ∷ʳ-⊒ t Σ
        v'  = loc (∈-∷ʳ Σ t)
        μ'  = (List∀.map (weaken-val ext) μ) all-∷ʳ (weaken-val ext v)
    in just (_ , μ' , v' , ext)

deref    :    ∀ {Σ Γ t} → t ∈ Σ → M Γ (Val t) Σ
deref x E μ = return (lookup μ x) E μ

update-store : ∀ {Σ t} → t ∈ Σ → Val t Σ → Store Σ → Store Σ
update-store ptr v μ = μ All[ ptr ]≔' v

lookup-store : ∀ {Σ t} → t ∈ Σ → Store Σ → Val t Σ
lookup-store x μ = lookup μ x

update   :    ∀ {Σ Γ t} → t ∈ Σ → Val t Σ → M Γ (λ _ → ⊤) Σ
update x v E μ = return tt E (update-store x v μ)

weaken : ∀ {i}{p : List Ty → Set i}⦃ w : Weakenable p ⦄ → ∀ {Σ Σ'} → Σ ⊑ Σ' → p Σ → p Σ'
weaken ⦃ w ⦄ ext v = Weakenable.weaken w ext v

_^_  : ∀ {Σ Γ}{p q : StoreTy → Set} → ⦃ w : Weakenable q ⦄ → M Γ p Σ → q Σ → M Γ (p ⊗ q) Σ
(f ^ x) E μ = case (f E μ) of λ {
  nothing → nothing ;
  (just (Σ , μ' , y , ext)) → just (Σ , μ' , (y , weaken ext x) , ext) }


eval : ℕ → ∀ {Σ Γ t} → Expr Γ t → M Γ (Val t) Σ
eval zero     _         =  timeout
eval (suc k)  unit      =  return unit
eval (suc k)  (var x)   =  getEnv >>= λ E → return (lookup E x)
eval (suc k)  (ƛ e)     =  getEnv >>= λ E → return ⟨ e , E ⟩
eval (suc k)  (l · r)   =  eval k l >>= λ{ ⟨ e , E ⟩ →
                           (eval k r ^ E) >>= λ{ (v , E) →
                           setEnv (v ∷ E) (eval k e) }}
eval (suc k)  (ref e)   =  eval k e >>= λ v → store v
eval (suc k)  (! e)     =  eval k e >>= λ{ (loc l) →
                           deref l }
eval (suc k)  (r ≔ e)   =  eval k r >>= λ{ (loc l) →
                           (eval k e ^ l) >>= λ{ (v , l) →
                           update l v >>= λ _ →
                           return unit }}
