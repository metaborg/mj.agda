module Experiments.StrongMonad (Type : Set) where

open import Level
open import Relation.Unary using (Pred)
open import Data.Product
open import Data.List.Most
open import Data.List.All as List∀
open import Data.List.Prefix
open import Function using (case_of_)

World = List Type

open import Experiments.Category (⊑-preorder {A = Type})
open Product

postulate Val : Type → MP₀

Store : World → Set
Store Σ = All (λ a → Val a · Σ) Σ

-- The monad takes monotone predicates over worlds
-- to monotone functions over stores in these worlds.
-- (this is a monotone-predicate transfomer)
M : ∀ {ℓ} → MP ℓ → MP ℓ
M P = mp (λ Σ → ∀ {Σ₁} → Σ ⊑ Σ₁ → Store Σ₁ → ∃ λ Σ₂ → Σ₂ ⊒ Σ₁ × Store Σ₂ × P · Σ₂)
  record { monotone = λ{
    w₀ f w₁ μ →
      case f (⊑-trans w₀ w₁) μ of λ{
        (Σ₂ , w₂ , μ₁ , v) → _ , w₂ , μ₁ , v
      }
    }
  }

-- η is the natural transformation between the identity functor and the functor M
η : ∀ {p}{P : MP p} → P ⇒ M P
η {P = P} =
  mk⇒ (λ p {Σ₁} ext μ → _ , ⊑-refl , μ , MP.monotone P ext p)

μ : ∀ {p}{P : MP p} → M (M P) ⇒ M P
μ = mk⇒ λ pc {Σ₁} ext μ →
  case pc ext μ of λ{
    (Σ₂ , ext₁ , μ₁ , f) →
      case f ⊑-refl μ₁ of λ{
        (Σ₃ , ext₂ , μ₂ , v) → _ , ⊑-trans ext₁ ext₂ , μ₂ , v
      }
  }

fmap : ∀ {p q}{P : MP p}{Q : MP q} → (P ⇒ Q) → M P ⇒ M Q
fmap F = mk⇒ λ x {Σ₁} ext μ → case x ext μ of λ{
    (Σ₂ , ext₁ , μ₁ , v) → Σ₂ , ext₁ , μ₁ , apply F v
  }

bind : ∀ {p q}{P : MP p}{Q : MP q} → (P ⇒ M Q) → M P ⇒ M Q
bind {Q = Q} F = μ {P = Q} ∘ fmap F

-- module Coherence where

  -- left-ident : ∀ {p q}{P : MP p}{Q : MP q}{F : P ⇒ M Q}{x} → (apply (bind F) (apply η x)) ⇒≡ F
  -- left-ident = ?


-- tensorial strength
ts : ∀ {p q}{P : MP p}{Q : MP q} → P ⊗ M Q ⇒ M (P ⊗ Q)
ts {P = P} = mk⇒ (λ x {Σ₁} ext μ →
    case x of λ{
      (px , m) →
        case m ext μ of λ{
          (_ , ext₁ , μ₁ , v ) → _ , ext₁ , μ₁ , (MP.monotone P (⊑-trans ext ext₁) px) , v
        }
    }
  )

