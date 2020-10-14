open import Relation.Binary using (Preorder)
open import Relation.Binary.PropositionalEquality

module Category.Monad.Monotone {ℓ}(pre : Preorder ℓ ℓ ℓ) where

open Preorder pre renaming (Carrier to I; _∼_ to _≤_; refl to ≤-refl)

open import Function
open import Level
open import Relation.Unary
open import Relation.Unary.Monotone pre
open import Relation.Unary.Monotone.Prefix
open import Relation.Unary.PredicateTransformer using (Pt)
open import Category.Monad.Predicate
open import Data.List
open import Data.Product
open import Data.List.All

record RawMPMonad (M : Pt I ℓ) : Set (suc ℓ) where

  infixl 1 _≥=_
  field
    return : ∀ {P} → P ⊆ M P
    _≥=_   : ∀ {P Q} → M P ⊆ ((P ↗ M Q) ⇒ M Q)

  -- we get the predicate-monad bind for free
  _>>=_ : ∀ {P Q} → M P ⊆ (λ i → (P ⊆ M Q) → M Q i)
  c >>= f = c ≥= λ i≤j pj → f pj

  -- which is only useful because we also get monadic strength for free:
  infixl 10 _^_
  _^_ : ∀ {P Q : Pred I ℓ}⦃ m : Monotone Q ⦄ → M P ⊆ (Q ⇒ M (P ∩ Q))
  c ^ qi = c ≥= λ {j} x≤j pj → return (pj , wk x≤j qi)

  ts : ∀ {P : Pred I ℓ} Q ⦃ m : Monotone Q ⦄ → M P ⊆ (Q ⇒ M (P ∩ Q))
  ts _ c qi = c ^ qi

  mapM : ∀ {P Q} → M P ⊆ ((P ↗ Q) ⇒ M Q)
  mapM m f = m ≥= (λ w p → return (f w p))

  sequenceM′ : ∀ {A : Set ℓ}{P : A → Pred I ℓ}{as} ⦃ mp : ∀ {a} → Monotone (P a) ⦄ {i k} → i ≤ k →
               All (λ a → ∀≥[ M (P a) ] i) as → M (λ j → All (λ a → P a j) as) k
  sequenceM′ _ [] = return []
  sequenceM′ {P}⦃ mp ⦄ le (x ∷ xs) = do
    px  , le  ← x le ^ le
    pxs , px ← sequenceM′ le xs ^ px
    return (px ∷ pxs)

  sequenceM : ∀ {A : Set ℓ}{P : A → Pred I ℓ}{as} ⦃ mp : ∀ {a} → Monotone (P a) ⦄ {i} →
              All (λ a → ∀≥[ M (P a) ] i) as → M (λ j → All (λ a → P a j) as) i
  sequenceM = sequenceM′ ≤-refl

  pmonad : RawPMonad {ℓ = ℓ} M
  pmonad = record
    { return? = return
    ; _=<?_ = λ f px → px >>= f }
