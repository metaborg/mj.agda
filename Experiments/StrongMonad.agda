module Experiments.StrongMonad (Type : Set) where

open import Level
open import Data.Product
open import Data.List.Most
open import Data.List.Prefix

World = List Type

open import Experiments.Category (⊑-preorder {A = Type})

postulate Val : Type → MP₀

Store : World → Set
Store Σ = All (λ a → Val a · Σ) Σ

M : MP₀ → World → Set
M P Σ = Store Σ → (∃ λ Σ' → Σ ⊑ Σ' × Store Σ' × P · Σ')

return : ∀ {Σ P} → P · Σ → M P Σ
return px = λ μ → _ , ⊑-refl , μ , px

bind : ∀ {Σ P Q} → (∀ {Σ} → P · Σ → M Q Σ) → M P Σ → M Q Σ
bind f m μ with m μ
... | _ , w₀ , μ' , v with f v μ'
... | _ , w₁ , μ'' , w = _ , ⊑-trans w₀ w₁ , μ'' , w

_^_ : ∀ {P Q Σ} → P · Σ → M Q Σ → M (P ⊗ Q) Σ
_^_ {P} px m μ with m μ
... | _ , w , μ' , qx = _ , w , μ' , (MP.monotone P w px , qx)
