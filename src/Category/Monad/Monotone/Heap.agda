import Relation.Unary.Monotone as Mono
open import Relation.Binary using (Preorder)
open import Relation.Binary.PropositionalEquality
open import Level

module Category.Monad.Monotone.Heap
  -- preordered heap types
  {ℓ}(pre : Preorder ℓ ℓ ℓ)
  -- types
  (T : Set ℓ)
  -- weakenable values
  (V : T → Preorder.Carrier pre → Set ℓ) ⦃ wkV : ∀ {a} → Mono.Monotone pre (V a) ⦄
  -- heaps indexed by the heap type
  (H : Preorder.Carrier pre → Set ℓ)
  -- weakenable heap type membership
  (_∈_ : T → Preorder.Carrier pre → Set ℓ) ⦃ wk∈ : ∀ {a} → Mono.Monotone pre (_∈_ a) ⦄ where

open Preorder pre renaming (Carrier to I; _∼_ to _≤_; refl to ≤-refl; trans to ≤-trans)

open import Data.Unit using (⊤; tt)
open import Relation.Unary hiding (_∈_)
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Unary.Monotone pre
open import Data.Product
open import Category.Monad
open import Category.Monad.Monotone pre
open import Category.Monad.Identity

open import Category.Monad.Monotone.State pre H

record HeapMonad (M : Pt I ℓ) : Set (suc ℓ) where
  field
    ⦃ super ⦄ : StateMonad M

  open StateMonad super public

  field
    store  : ∀ {a} → V a ⊆ M (λ W → a ∈ W)
    modify : ∀ {a} → _∈_ a ⊆ V a ⇒ M (λ W' → Lift ⊤)
    deref  : ∀ {a} → _∈_ a ⊆ M (V a)

  module _ ⦃ m : RawMPMonad M ⦄ where
    open RawMPMonad m
    open import Data.List.All as All

    storeₙ  : ∀ {W as} → All (λ a → V a W) as → M (λ W' → All (λ a → a ∈ W') as) W
    storeₙ vs = sequenceM (All.map (λ v {x} ext → store (wk ext v)) vs)
