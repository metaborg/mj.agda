{-# OPTIONS --show-implicit #-}
open import Relation.Binary.PropositionalEquality

module Experiments.Ref (funext : ∀ {a b} → Extensionality a b) where

open import Level
open import Data.Nat
import Data.Unit as Unit
open import Data.List
open import Data.List.Most
open import Data.Product hiding (swap)
open import Data.Maybe as Maybe hiding (All)
open import Function as Fun using (case_of_)
import Relation.Binary.PropositionalEquality as PEq
open PEq.≡-Reasoning

data Ty : Set where
  unit : Ty
  ref  : Ty → Ty

open import Experiments.Category (⊑-preorder {A = Ty})
open Product

data Expr : Ty → Set where
  unit  : Expr unit
  ref   : ∀ {t} → Expr t → Expr (ref t)
  !_    : ∀ {t} → Expr (ref t) → Expr t
  _≔_   : ∀ {t} → Expr (ref t) → Expr t → Expr unit

Val : Ty → MP₀
Val t = mp (Val' t) (record {
    monotone = λ{ c~c' unit → unit ; c~c' (ref x) → ref (∈-⊒ x c~c') };
    monotone-refl = λ{ unit → refl ; (ref x) → cong ref ∈-⊒-refl };
    monotone-trans = λ p c~c' c'~c'' → {!!}
  })
  module Values where
    data Val' : Ty → List Ty → Set where
      unit   : ∀ {Σ} → Val' unit Σ
      ref    : ∀ {Σ t} → t ∈ Σ → Val' (ref t) Σ

open import Experiments.StrongMonad Ty Val funext

mkunit : ⊤ ⇒ Val unit
mkunit = mk⇒ (λ _ → Values.unit) λ c~c' → refl

alloc : ∀ {a} → Val a ⇒ M (Val (ref a))
alloc {a} = mk⇒
  (λ v Σ₁ ext μ₁ →
    let ext' = ∷ʳ-⊒ a Σ₁ in
      (Σ₁ ∷ʳ a) ,
      ext' ,
      ((map-all (MP.monotone (Val _) ext') μ₁) all-∷ʳ MP.monotone (Val _) (⊑-trans ext ext') v) ,
      Values.ref (∈-∷ʳ Σ₁ a))
  (λ c~c' → {!!})

load : ∀ {a} → Val (ref a) ⇒ M (Val a)
load  {a} = mk⇒
  (λ v Σ₁ ext μ₁ → case v of λ{
    (Values.ref x) → Σ₁ , ⊑-refl , μ₁ , (∈-all (∈-⊒ x ext) μ₁)
  })
  (λ c~c' → {!!})

store : ∀ {a} → (Val (ref a) ⊗ Val a) ⇒ M ⊤
store = mk⇒
  (λ x Σ₁ ext μ₁ → case x of λ{
    (Values.ref l , v) → Σ₁ , ⊑-refl , (μ₁ All[ ∈-⊒ l ext ]≔' MP.monotone (Val _) ext v) , Unit.tt
  })
  (λ c~c' → {!!})

eval : ∀ {a} → Expr a → ⊤ ⇒ M (Val a)
eval unit = η (Val _) ∘ mkunit
eval (ref e) = μ (Val _) ∘ fmap alloc ∘ eval e
eval (! e) = μ (Val _) ∘ fmap load ∘ eval e
eval (e₁ ≔ e₂) =
    fmap mkunit
  ∘ μ ⊤
  ∘ fmap store
  ∘ μ ((Val _) ⊗ (Val _))
  ∘ fmap (ts' (Val _)(Val _))
  ∘ ts (M (Val _))(Val _)
  ∘ ⟨ eval e₁ , eval e₂ ⟩

