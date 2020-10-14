open import Relation.Binary using (Preorder)
open import Relation.Binary.PropositionalEquality
open import Level

module Category.Monad.Monotone.State {ℓ}(pre : Preorder ℓ ℓ ℓ)(H : Preorder.Carrier pre → Set ℓ) where

open Preorder pre renaming (Carrier to I; _∼_ to _≤_; refl to ≤-refl; trans to ≤-trans)

open import Data.Unit using (⊤; tt)
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Unary.Monotone pre
open import Data.Product
open import Data.List.All
open import Category.Monad
open import Category.Monad.Monotone pre
open import Category.Monad.Identity

MST : (Set ℓ → Set ℓ) → Pt I ℓ
MST M P = H ⇒ (λ i → M (∃ λ j → i ≤ j × H j × P j))

MSt : Pt I ℓ
MSt = MST Identity

record StateMonad (M : Pt I ℓ) : Set (suc ℓ) where
  field
    runState : ∀ {P} → (H ↗ H ∩ P) ⊆ M P

  get : ∀ {i} → M H i
  get = runState λ _ μ → μ , μ

module _ {M}⦃ Mon : RawMonad {ℓ} M ⦄ where
  private module M = RawMonad Mon

  instance
    open RawMPMonad hiding (_>>=_; ts)
    mst-monad : RawMPMonad (MST M)
    return mst-monad px μ = M.return (_ , ≤-refl , μ , px)
    _≥=_ mst-monad c f  μ = c μ M.>>= λ where
      (i₁ , ext₁ , μ₁ , pv) → (f ext₁ pv μ₁) M.>>= λ where
        (i₂ , ext₂ , μ₂ , pw) → M.return (i₂ , ≤-trans ext₁ ext₂ , μ₂ , pw)

    open StateMonad
    mst-monad-ops : StateMonad (MST M)
    runState (mst-monad-ops) f μ = let μ' , p = f ≤-refl μ in M.return (_ , ≤-refl , μ' , p)
