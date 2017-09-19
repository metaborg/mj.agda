open import Relation.Binary.PropositionalEquality

module Experiments.StrongMonad (Type : Set)(funext : ∀ {a b} → Extensionality a b)  where

open import Level
open import Relation.Unary using (Pred)
open import Data.Product
open import Data.List.Most
open import Data.List.All as List∀
open import Data.List.Prefix
open import Function using (case_of_)
open ≡-Reasoning

World = List Type

open import Experiments.Category (⊑-preorder {A = Type})
open Product

postulate Val : Type → MP₀

Store : World → Set
Store Σ = All (λ a → Val a · Σ) Σ

-- functional extensionality for the type of predicates that our monad builds
meq : ∀ {Σ' b}{B : World → Set b}{f g : (Σ : World) → Σ' ⊑ Σ → Store Σ → B Σ} →
      (∀ Σ → (ext : Σ' ⊑ Σ) → (μ : Store Σ) → f Σ ext μ ≡ g Σ ext μ) →
      f ≡ g
meq p = funext λ Σ → funext λ ext → funext λ μ → p Σ ext μ

-- The monad takes monotone predicates over worlds
-- to monotone functions over stores in these worlds.
-- (this is a monotone-predicate transfomer)
M : ∀ {ℓ} → MP ℓ → MP ℓ
M P = mp (λ Σ → ∀ Σ₁ → Σ ⊑ Σ₁ → Store Σ₁ → ∃ λ Σ₂ → Σ₂ ⊒ Σ₁ × Store Σ₂ × P · Σ₂)
  record {
    monotone = λ w₀ f Σ w₁ μ → f Σ (⊑-trans w₀ w₁) μ ;
    monotone-refl = λ f → meq (λ Σ₁ _ μ → cong (λ u → f Σ₁ u μ) ⊑-trans-refl) ;
    monotone-trans = λ f w₀ w₁ → meq (λ Σ₁ w₂ μ → cong (λ u → f Σ₁ u μ) (sym ⊑-trans-assoc))
  }

-- η is the natural transformation between the identity functor and the functor M
η : ∀ {p}(P : MP p) → P ⇒ M P
η P =
  mk⇒
    (λ p _ ext μ → _ , ⊑-refl , μ , MP.monotone P ext p)
    (λ c~c' {p} → begin
      (λ z ext μ → z , ⊑-refl , μ , MP.monotone P ext (MP.monotone P c~c' p))
        ≡⟨ meq (λ z ext μ → cong (λ u → z , ⊑-refl , μ , u) (sym (MP.monotone-trans P p c~c' ext))) ⟩
      (λ z ext μ → z , ⊑-refl , μ , MP.monotone P (⊑-trans c~c' ext) p)
        ≡⟨ refl ⟩
      MP.monotone (M P) c~c' (λ z ext μ → z , ⊑-refl , μ , MP.monotone P ext p)
    ∎)

μ : ∀ {p}{P : MP p} → M (M P) ⇒ M P
μ = mk⇒
  (λ pc Σ₁ ext μ →
    case pc _ ext μ of λ{
      (Σ₂ , ext₁ , μ₁ , f) →
        case f _ ⊑-refl μ₁ of λ{
          (Σ₃ , ext₂ , μ₂ , v) → _ , ⊑-trans ext₁ ext₂ , μ₂ , v
        }
    })
  (λ c~c' → refl)

fmap : ∀ {p q}{P : MP p}{Q : MP q} → (P ⇒ Q) → M P ⇒ M Q
fmap F = mk⇒
  (λ x Σ₁ ext μ → case x _ ext μ of λ{
    (Σ₂ , ext₁ , μ₁ , v) → Σ₂ , ext₁ , μ₁ , apply F v
  })
  (λ c~c' → refl)

bind : ∀ {p q}{P : MP p}{Q : MP q} → (P ⇒ M Q) → M P ⇒ M Q
bind {Q = Q} F = μ {P = Q} ∘ fmap F

module Coherence where

  -- We prove that η is the component of a natural transformation.
  η-natural : ∀ {p q}(P : MP p)(Q : MP q)(F : P ⇒ Q) → η Q ∘ F ⇒≡ (fmap F) ∘ η P
  η-natural P Q F p =
    begin
      apply (η Q ∘ F) p
        ≡⟨ refl ⟩
      apply (η Q) (apply F p)
        ≡⟨ refl ⟩
      (λ Σ ext μ → Σ , ⊑-refl , μ , MP.monotone Q ext (apply F p))
        ≡⟨ meq (λ Σ ext μ → cong (λ u → Σ , ⊑-refl , μ , u) (sym (monotone-comm F ext))) ⟩
      (λ Σ ext μ → Σ , ⊑-refl , μ , apply F (MP.monotone P ext p))
        ≡⟨ refl ⟩
      apply (fmap F) (λ Σ ext μ → Σ , ⊑-refl , μ , MP.monotone P ext p)
        ≡⟨ refl ⟩
      apply (fmap F) (apply (η P) p)
        ≡⟨ refl ⟩
      apply (fmap F ∘ η P) p
    ∎

{-
-- tensorial strength
ts : ∀ {p q}{P : MP p}{Q : MP q} → P ⊗ M Q ⇒ M (P ⊗ Q)
ts {P = P} = mk⇒
  (λ x Σ₁ ext μ →
    case x of λ{
      (px , m) →
        case m _ ext μ of λ{
          (_ , ext₁ , μ₁ , v ) → _ , ext₁ , μ₁ , (MP.monotone P (⊑-trans ext ext₁) px) , v
        }
    }
  )
  {!!}
-}
