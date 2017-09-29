{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Relation.Unary using (Pred)
open import Data.Product hiding (swap; curry)
open import Data.List.Most
open import Data.List.All as List∀
open import Data.List.Prefix
open import Function as Fun using (case_of_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

import Experiments.Category as Cat

module Experiments.StrongMonad
  (Type : Set)
  (Val : Type → Cat.MP₀ (⊑-preorder {A = Type}))
  (funext : ∀ {a b} → Extensionality a b) where

open import Relation.Binary.PropositionalEquality.Extensionality funext

open Cat (⊑-preorder {A = Type})
open Product

World = List Type

Store : World → Set
Store Σ = All (λ a → Val a · Σ) Σ

import Relation.Binary.HeterogeneousEquality as H
module HR = H.≅-Reasoning

mcong : ∀ {Σₛ Σ Σ' ℓ}{P : MP ℓ}
        {μ : Store Σ}{μ' : Store Σ'}{p : Σ ⊒ Σₛ}{p' : Σ' ⊒ Σₛ}{q : P · Σ}{q' : P · Σ'} →
        Σ ≡ Σ' → p H.≅ p' → μ H.≅ μ' → q H.≅ q' → (Σ , p , μ , q) ≡ (Σ' , p' , μ' , q')
mcong refl H.refl H.refl H.refl = refl

-- The monad takes monotone predicates over worlds
-- to monotone functions over stores in these worlds.
M : ∀ {ℓ} → MP ℓ → MP ℓ
M P = mp (λ Σ → ∀ Σ₁ → (ext : Σ ⊑ Σ₁) → (μ : Store Σ₁) → ∃ λ Σ₂ → Σ₂ ⊒ Σ₁ × Store Σ₂ × P · Σ₂)
  record {
    monotone = λ w₀ f Σ w₁ μ → f Σ (⊑-trans w₀ w₁) μ ;
    monotone-refl = λ f → funext³ (λ Σ₁ _ μ → cong (λ u → f Σ₁ u μ) ⊑-trans-refl) ;
    monotone-trans = λ f w₀ w₁ → funext³ (λ Σ₁ w₂ μ → cong (λ u → f Σ₁ u μ) (sym ⊑-trans-assoc))
  }

-- η is the natural transformation between the identity functor and the functor M
η : ∀ {p}(P : MP p) → P ⇒ M P
η P =
  mk⇒
    (λ p Σ ext μ → Σ , ⊑-refl , μ , MP.monotone P ext p)
    (λ c~c' {p} → begin
      (λ z ext μ → z , ⊑-refl , μ , MP.monotone P ext (MP.monotone P c~c' p))
        ≡⟨ funext³ (λ z ext μ → cong (λ u → z , ⊑-refl , μ , u) (sym (MP.monotone-trans P p c~c' ext))) ⟩
      (λ z ext μ → z , ⊑-refl , μ , MP.monotone P (⊑-trans c~c' ext) p)
        ≡⟨ refl ⟩
      MP.monotone (M P) c~c' (λ z ext μ → z , ⊑-refl , μ , MP.monotone P ext p)
    ∎)

μ : ∀ {p}(P : MP p) → M (M P) ⇒ M P
μ P = mk⇒
  (λ pc Σ₁ ext μ →
    case pc Σ₁ ext μ of λ{
      (Σ₂ , ext₁ , μ₁ , f) →
        case f Σ₂ ⊑-refl μ₁ of λ{
          (Σ₃ , ext₂ , μ₂ , v) → Σ₃ , ⊑-trans ext₁ ext₂ , μ₂ , v
        }
    })
  (λ c~c' → refl)

fmap : ∀ {p q}{P : MP p}{Q : MP q} → (P ⇒ Q) → M P ⇒ M Q
fmap F = mk⇒
  (λ x Σ₁ ext μ → case x Σ₁ ext μ of λ{
    (Σ₂ , ext₁ , μ₁ , v) → Σ₂ , ext₁ , μ₁ , apply F v
  })
  (λ c~c' → refl)

bind : ∀ {p q}{P : MP p}(Q : MP q) → (P ⇒ M Q) → M P ⇒ M Q
bind Q F = μ Q ∘ fmap F

open Exponential (sym ⊑-trans-assoc) ⊑-trans-refl ⊑-trans-refl'

module Coherence where
  -- We prove that η is the component of a natural transformation between the functors
  -- 𝕀 and M where 𝕀 is the identity functor.
  η-natural : ∀ {p q}(P : MP p)(Q : MP q)(F : P ⇒ Q) → η Q ∘ F ⇒≡ (fmap F) ∘ η P
  η-natural P Q F p =
    begin
      apply (η Q ∘ F) p
        ≡⟨ refl ⟩
      apply (η Q) (apply F p)
        ≡⟨ refl ⟩
      (λ Σ ext μ → Σ , ⊑-refl , μ , MP.monotone Q ext (apply F p))
        ≡⟨ funext³ (λ Σ ext μ → cong (λ u → Σ , ⊑-refl , μ , u) (sym (monotone-comm F ext))) ⟩
      (λ Σ ext μ → Σ , ⊑-refl , μ , apply F (MP.monotone P ext p))
        ≡⟨ refl ⟩
      apply (fmap F) (λ Σ ext μ → Σ , ⊑-refl , μ , MP.monotone P ext p)
        ≡⟨ refl ⟩
      apply (fmap F) (apply (η P) p)
        ≡⟨ refl ⟩
      apply (fmap F ∘ η P) p
    ∎

  -- We prove that μ is the component of a natural transformation between
  -- the functors M² and M.
  μ-natural : ∀ {p q}(P : MP p)(Q : MP q)(F : P ⇒ Q) → μ Q ∘ (fmap (fmap F)) ⇒≡ (fmap F) ∘ μ P
  μ-natural P Q F = λ p → refl

  -- from these facts we can prove the monad laws
  left-id : ∀ {p}{P : MP p} → μ P ∘ fmap (η P) ⇒≡ id (M P)
  left-id {P = P} p = funext³
    λ Σ₁ ext μ₁ → mcong {P = P} refl (lem refl) H.refl (H.≡-to-≅ (MP.monotone-refl P _))
    where
      lem : ∀ {Σ Σ' Σ'' : World}{xs : Σ'' ⊒ Σ'}{ys : Σ'' ⊒ Σ} → Σ ≡ Σ' →  ⊑-trans xs ⊑-refl H.≅ ys
      lem {xs = xs}{ys} refl with ⊑-unique xs ys
      ... | refl = H.≡-to-≅ ⊑-trans-refl'

  {-}
  TODO
  right-id : ∀ {p}{P : MP p} → μ P ∘ (η (M P)) ⇒≡ id (M P)
  right-id {P = P} p = meq λ Σ₁ ext μ₁ → mcong {!!} {!!} {!!} {!!}
  -}

  -- if we have a (M³ P) then it doesn't matter if we join
  -- the outer or inner ones first.
  assoc : ∀ {p}{P : MP p} → μ P ∘ (fmap (μ P)) ⇒≡ μ P ∘ μ (M P)
  assoc {P = P} p = funext³ λ Σ₁ ext μ → mcong {P = P} refl (H.≡-to-≅ ⊑-trans-assoc) H.refl H.refl

module Strong where
  -- tensorial strength
  ts : ∀ {p q}(P : MP p)(Q : MP q) → P ⊗ M Q ⇒ M (P ⊗ Q)
  ts P Q = mk⇒
    (λ x Σ₁ ext μ →
      case (proj₂ x) Σ₁ ext μ of λ{
        (_ , ext₁ , μ₁ , v ) → _ , ext₁ , μ₁ , (MP.monotone P (⊑-trans ext ext₁) (proj₁ x)) , v
      }
    )
    (λ c~c' →
      funext³ λ Σ₁ ext μ₁ →
      mcong {P = (P ⊗ Q)} refl H.refl H.refl (
        H.cong₂ {A = P · _}{B = λ _ → Q · _} (λ u v → u , v)
          (H.≡-to-≅ (begin
            MP.monotone P (⊑-trans ext _) _
              ≡⟨ (MP.monotone-trans P _ _ _) ⟩
            MP.monotone P _ (MP.monotone P ext (MP.monotone P c~c' _))
              ≡⟨ cong (λ x → MP.monotone P _ x) (sym ((MP.monotone-trans P _ _ _))) ⟩
            MP.monotone P _ (MP.monotone P (⊑-trans c~c' ext) _)
              ≡⟨ sym ((MP.monotone-trans P _ _ _)) ⟩
            MP.monotone P (⊑-trans (⊑-trans c~c' ext) _) _
          ∎))
          H.refl
      ))

  ts' : ∀ {p q}(P : MP p)(Q : MP q) → M P ⊗ Q ⇒ M (P ⊗ Q)
  ts' P Q = fmap (swap Q P) ∘ ts Q P ∘ swap _ _

  -- postulate
  diagram₁ : ∀ {ℓ}{P : MP ℓ} → fmap {P = ⊤ ⊗ P} (π₂ {P = ⊤}) ∘ ts ⊤ P ⇒≡ π₂ {P = ⊤}
  diagram₁ = λ p → refl

  diagram₂ : ∀ {ℓ₁ ℓ₂ ℓ₃}{A : MP ℓ₁}{B : MP ℓ₂}{C : MP ℓ₃} →
            fmap (comm A B C) ∘ ts (A ⊗ B) C ⇒≡ ts A (B ⊗ C) ∘ xmap (id A) (ts B C) ∘ comm A B (M C)
  diagram₂ = λ p → refl

  diagram₃ : ∀ {ℓ₁ ℓ₂}(A : MP ℓ₁)(B : MP ℓ₂) →
             η (A ⊗ B) ⇒≡ ts A B ∘ xmap (id A) (η B)
  diagram₃ A B =
    λ{ (a , b)  →
       funext³ λ Σ ext r →
         mcong {P = A ⊗ B}
               refl
               H.refl
               H.refl
               (H.≡-to-≅
                 (cong₂ (λ x₁ x₂ → x₁ , x₂)
                   (cong₂ (λ ext a → MP.monotone A ext a)
                     (trans (sym ⊑-trans-refl')
                       (cong (λ r → ⊑-trans ext r)
                         refl))
                     refl)
                   (cong (λ x → x) refl))
                 )}

  postulate
    diagram₄ : ∀ {ℓ₁ ℓ₂}{A : MP ℓ₁}{B : MP ℓ₂} →
              ts A B ∘ xmap (id A) (μ B) ⇒≡ μ (A ⊗ B) ∘ fmap (ts A B) ∘ ts A (M B)
    -- diagram₄ = {!!}

  -- internal fmap
  fmap' : ∀ {p q}{P : MP p}{Q : MP q} → (Q ^ P) ⇒ (M Q) ^ (M P)
  fmap' {P = P}{Q} = curry (fmap ε ∘ ts (Q ^ P) P)

  -- internal bind
  bind' : ∀ {p q}{P : MP p}(Q : MP q) → (M P ⊗ (M Q ^ P)) ⇒ M Q
  bind' {P = P} Q =
    μ Q
    ∘ fmap (ε ∘ swap P (M Q ^ P))
    ∘ ts' P (M Q ^ P)
