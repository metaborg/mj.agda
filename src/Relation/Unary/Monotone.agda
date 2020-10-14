open import Relation.Binary hiding (_⇒_)
open import Level

module Relation.Unary.Monotone {c i}(pre : Preorder i c i) where

open Preorder pre renaming (Carrier to I; _∼_ to _≤_)
open import Relation.Unary
open import Data.Product hiding (map)
open import Data.List
open import Function

record Monotone {ℓ}(p : Pred I ℓ) : Set (i ⊔ ℓ) where
  field wk : ∀ {i j} → i ≤ j → p i → p j

open Monotone
open Monotone ⦃...⦄ public

∀≥[_] : ∀ {ℓ} → Pred I ℓ → Pred I (i ⊔ ℓ)
∀≥[ P ] i = ∀ {j} → i ≤ j → P j

∃≥[_] : ∀ {ℓ} → Pred I ℓ → Pred I (i ⊔ ℓ)
∃≥[ P ] i = ∃ λ j → i ≤ j × P j

infixr 4 _↗_
_↗_ : ∀ {ℓ} → Pred I ℓ → Pred I ℓ → Pred I (i ⊔ ℓ)
(P ↗ Q) = ∀≥[ P ⇒ Q ]

instance
  ∀≥-monotone : ∀ {ℓ}{P : Pred I ℓ} → Monotone ∀≥[ P ]
  wk ∀≥-monotone ext f ext' = f (trans ext ext')

  mono-∩ : ∀ {i j}{p : Pred I i}{q : Pred I j}
             ⦃ wp : Monotone p ⦄ ⦃ wq : Monotone q ⦄ → Monotone (p ∩ q)
  wk (mono-∩ ⦃ wp ⦄ ⦃ wq ⦄) ext (x , y) = (wk wp ext x , wk wq ext y)

  list-monotone : ∀ {B : Pred I i}⦃ wb : Monotone B ⦄ → Monotone (λ W → List (B W))
  wk (list-monotone ⦃ wₐ ⦄) ext v = map (wk wₐ ext) v

  open import Data.List.All as All
  all-monotone : ∀ {b i}{B : Set b}{xs : List B}{C : B → Pred I i}
                 ⦃ wₐ : ∀ x → Monotone (C x) ⦄ →
                 Monotone (λ ys → All (λ x → C x ys) xs)
  wk (all-monotone ⦃ wₐ ⦄) ext v = All.map (λ {a} y → wk (wₐ a) ext y) v

  open import Data.Vec using (Vec)
  open import Data.Vec.All as VAll
  vec-all-monotone : ∀ {b i n}{B : Set b}{xs : Vec B n}{C : B → Pred I i}
                 ⦃ wₐ : ∀ x → Monotone (C x) ⦄ →
                 Monotone (λ ys → VAll.All (λ x → C x ys) xs)
  wk (vec-all-monotone ⦃ wₐ ⦄) ext v = VAll.map (λ {a} y → wk (wₐ a) ext y) v

  ≤-mono : ∀ {i} → Monotone (_≤_ i)
  wk ≤-mono = flip trans

  open import Data.Maybe as Maybe
  maybe-monotone : ∀ {i}{P : Pred I i} ⦃ mono : Monotone P ⦄ → Monotone (λ W → Maybe (P W))
  wk (maybe-monotone ⦃ mono ⦄) ext mv = Maybe.map (wk mono ext) mv
