open import Relation.Binary.PropositionalEquality

module Experiments.STLCRef
       (funext : ∀ {a b} → Extensionality a b) where

open import Level
open import Data.Nat
open import Data.Unit as Unit
open import Data.List
open import Data.List.Most
open import Data.Product
open import Data.Maybe as Maybe hiding (All)
open import Function as Fun using (case_of_)
import Relation.Binary.PropositionalEquality as PEq
open PEq.≡-Reasoning

data Ty : Set where
  unit : Ty
  arrow : (a b : Ty) → Ty
  ref  : Ty → Ty

open import Experiments.Category (⊑-preorder {A = Ty})

Ctx     = List Ty
StoreTy = List Ty

data Expr (Γ : List Ty) : Ty → Set where
  var : ∀ {t} → t ∈ Γ → Expr Γ t
  ƛ     : ∀ {a b} → Expr (a ∷ Γ) b → Expr Γ (arrow a b)
  app   : ∀ {a b} → Expr Γ (arrow a b) → Expr Γ a → Expr Γ b
  unit  : Expr Γ unit
  ref   : ∀ {t} → Expr Γ t → Expr Γ (ref t)
  !_    : ∀ {t} → Expr Γ (ref t) → Expr Γ t
  _≔_   : ∀ {t} → Expr Γ (ref t) → Expr Γ t → Expr Γ unit

mutual
  Env : (Γ : Ctx)(Σ : StoreTy) → Set
  Env Γ Σ = All (λ t → Val t Σ) Γ

  data Val : Ty → List Ty → Set where
    unit   : ∀ {Σ} → Val unit Σ
    ⟨_,_⟩  : ∀ {Σ Γ a b} → Expr (a ∷ Γ) b → Env Γ Σ → Val (arrow a b) Σ
    loc    : ∀ {Σ t} → t ∈ Σ → Val (ref t) Σ

weaken-all : ∀ {i}{A : Set i}{j}{B : Set j}{xs : List B}
               {k}{C : B → List A → Set k}( wₐ : ∀ {x} {bs cs} → bs ⊑ cs → C x bs → C x cs) →
               ∀ {bs cs} → bs ⊑ cs → All (λ x → C x bs) xs → All (λ x → C x cs) xs
weaken-all wₐ ext x = map-all (λ y → wₐ ext y) x

mutual
  weaken-val  :  ∀ {a : Ty}{Σ Σ' : StoreTy} → Σ ⊑ Σ' → Val a Σ → Val a Σ'
  weaken-val ext unit      = unit
  weaken-val ext ⟨ e , E ⟩ = ⟨ e , weaken-env ext E ⟩
  weaken-val ext (loc l)   = loc (∈-⊒ l ext)

  weaken-env  :  ∀ {Γ}{Σ Σ' : StoreTy} → Σ ⊑ Σ' → Env Γ Σ → Env Γ Σ'
  weaken-env ext (v ∷ vs)  = weaken-val ext v ∷ weaken-env ext vs
  weaken-env ext []        = []

  -- weaken-env : ∀ {Γ}{Σ Σ' : StoreTy} → Σ ⊑ Σ' → Env Γ Σ → Env Γ Σ'
  -- weaken-env ext E = weaken-all weaken-val ext E

import Relation.Binary.HeterogeneousEquality as H

mutual
  clo-cong : ∀ {Γ a t Σ}{e e' : Expr (a ∷ Γ) t}{E E' : Env Γ Σ} →
             e ≡ e' → E ≡ E' → ⟨ e , E ⟩ ≡ ⟨ e' , E' ⟩
  clo-cong refl refl = refl

  mono-val-refl  :  ∀ {t c}{ext : c ⊑ c}(p : Val t c) → 
                        weaken-val ext p ≡ p
  mono-val-refl unit      = refl
  mono-val-refl ⟨ e , E ⟩ = clo-cong refl (mono-env-refl E)
  mono-val-refl (loc l)   = {!!}

  mono-env-refl  :  ∀ {Γ c}{ext : c ⊑ c}(p : Env Γ c) → 
                        weaken-env ext p ≡ p
  mono-env-refl []       = refl
  mono-env-refl (v ∷ vs) = {!!}

  Val' : Ty → MP₀
  Val' t = mp (Val t)
              (record { monotone = weaken-val ;
                        monotone-refl = mono-val-refl ;
                        monotone-trans = {!!} })

  Env' : List Ty → MP₀
  Env' Γ = mp (Env Γ)
              (record { monotone = weaken-env ;
                        monotone-refl = mono-env-refl ;
                        monotone-trans = {!!} })

open import Experiments.StrongMonad Ty Val' funext

meq' : ∀ {Σ' b}{B : World → Set b}{Γ}{f g : (Σ : World) → Σ' ⊑ Σ → Env' Γ · Σ → Store Σ → B Σ} →
       (∀ Σ → (ext : Σ' ⊑ Σ) → (E : Env' Γ · Σ) → (μ : Store Σ) → f Σ ext E μ ≡ g Σ ext E μ) →
       f ≡ g
meq' p = funext λ Σ → funext λ ext → funext λ E → funext λ μ → p Σ ext E μ

M' : ∀ {ℓ} → List Ty → MP ℓ → MP ℓ
M' Γ P = mp (λ Σ → ∀ Σ₁ → Σ ⊑ Σ₁ → Env' Γ · Σ₁ → Store Σ₁ →
         Maybe (∃ λ Σ₂ → Σ₂ ⊒ Σ₁ × Store Σ₂ × P · Σ₂))
  record {
    monotone = λ w₀ f Σ w₁ E μ → f Σ (⊑-trans w₀ w₁) E μ ;
    monotone-refl = λ f → meq' (λ Σ₁ _ E μ → cong (λ u → f Σ₁ u E μ) ⊑-trans-refl) ;
    monotone-trans = λ f w₀ w₁ → meq' (λ Σ₁ w₂ E μ → cong (λ u → f Σ₁ u E μ) (sym ⊑-trans-assoc))
  }

One : MP₀
One = mp (λ _ → Unit.⊤) ((record {
    monotone = λ _ _ → tt ;
    monotone-refl = λ _ → refl ;
    monotone-trans = λ _ _ _ → refl
  }))

-- one : ∀ {Γ} → M' Γ One
-- one = ?

η' : ∀ {Γ}{p}(P : MP p) → P ⇒ M' Γ P
η' P =
  mk⇒
    (λ p Σ ext _ μ → just (Σ , ⊑-refl , μ , MP.monotone P ext p))
    (λ c~c' {p} → begin
      (λ z ext E μ → just (z , ⊑-refl , μ , MP.monotone P ext (MP.monotone P c~c' p)))
        ≡⟨ meq' (λ z ext E μ → cong (λ u → just (z , ⊑-refl , μ , u)) (sym (MP.monotone-trans P p c~c' ext))) ⟩
      (λ z ext E μ → just (z , ⊑-refl , μ , MP.monotone P (⊑-trans c~c' ext) p))
        ≡⟨ refl ⟩
      MP.monotone (M' _ P) c~c' (λ z ext E μ → just (z , ⊑-refl , μ , MP.monotone P ext p))
    ∎)

-- necessary because Agda's unification is shaky for pattern matching
-- lambdas
join : ∀ {l}{a : Set l} → Maybe (Maybe a) → Maybe a
join nothing         = nothing
join (just nothing)  = nothing
join (just (just x)) = just x

μ' : ∀ {Γ}{p}(P : MP p) → M' Γ (M' Γ P) ⇒ M' Γ P
μ' P = mk⇒
  (λ pc Σ₁ ext E μ →
    join (case pc Σ₁ ext E μ of (Maybe.map (λ{
      (Σ₂ , ext₁ , μ₁ , f) →
        case f Σ₂ ⊑-refl (weaken-env ext₁ E) μ₁ of (Maybe.map (λ{
          (Σ₃ , ext₂ , μ₂ , v) →
            Σ₃ , ⊑-trans ext₁ ext₂ , μ₂ , v
        }))
    }))))
  (λ c~c' → refl)

fmap' : ∀ {Γ p q}{P : MP p}{Q : MP q} → (P ⇒ Q) → M' Γ P ⇒ M' Γ Q
fmap' F = mk⇒
  (λ x Σ₁ ext E μ → case x Σ₁ ext E μ of Maybe.map (λ{
    (Σ₂ , ext₁ , μ₁ , v) → Σ₂ , ext₁ , μ₁ , apply F v
  }))
  (λ c~c' → refl)



bind' : ∀ {p q}{P : MP p}{Q : MP q}{Γ} → (P ⇒ M' Γ Q) → M' Γ P ⇒ M' Γ Q
bind' {Q = Q} F = μ' Q ∘ fmap' F

timeout  : ∀ {p : MP₀}{Γ} → M' Γ One ⇒ M' Γ p
timeout = mk⇒ (λ _ _ _ _ _ → nothing) (λ _ → refl)

-- -- getEnv  :  ∀ {Γ Σ} → M' Γ (Env' Γ) · Σ
-- -- getEnv {Γ} _ _ E = apply (η' (Env' Γ)) E _ ⊑-refl E

-- getEnv  :  ∀ {Γ} → One ⇒ M' Γ (Env' Γ)
-- getEnv = mk⇒ (λ x Σ₁ ext E μ → just ( Σ₁ , ⊑-refl , μ , E )) (λ _ → refl)

-- -- setEnv   :    ∀ {Σ Γ Γ'}{p : List Ty → Set} → Env Γ Σ → M Γ p Σ → M Γ' p Σ

eval : ℕ → ∀ {Γ t} → Expr Γ t → M' Γ One ⇒ M' Γ (Val' t)
eval zero    _       = timeout {Val' _}
eval (suc k) unit    = {!!} -- bind' {_} {_} { (mk⇒ (λ x → apply (η' (Val' unit)) unit) (λ c~c' → refl))
-- -- eval (suc k) (var x) = -- apply {!!} {!!}
eval _ _ = {!!}
