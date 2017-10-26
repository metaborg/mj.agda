open import Categorical.Preorder

module Categorical.MonotonePredicates.Monads.State {ℓ}
  (po : PreorderPlus ℓ ℓ ℓ)
  (Store : PreorderPlus.Carrier po → Set ℓ) where

open import Categorical.MonotonePredicates po
open PreorderPlus po hiding (po)

open import Level

open import Data.Product
open import Categories.Category
open import Categories.Agda
open import Categories.Functor hiding (_≡_; assoc; identityˡ; identityʳ)
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.Monad
open import Categories.Monad.Strong
open import Categories.Support.Equivalence
open import Relation.Binary.PropositionalEquality as PEq using () renaming (_≡_ to _≣_)

open Category

private
  module MP = Category MP

∃[_]-setoid_ : ∀ {ℓ s₁ s₂} → (A : Set ℓ) → (A → Setoid s₁ s₂) → Setoid _ _
∃[ A ]-setoid B = record
   { Carrier = ∃ λ a → B.Carrier a
   ; _≈_ = λ{ (l , r) (l' , r') → ∃ λ (p : l ≣ l') → B._≈_ l' (PEq.subst B.Carrier p r) r' }
   ; isEquivalence = record {
     refl = PEq.refl , (B.refl _) ;
     sym = λ{ (PEq.refl , q) → PEq.refl , B.sym _ q };
     trans = λ{ (PEq.refl , p) (PEq.refl , q) → PEq.refl , B.trans _ p q }}
   }
  where
    module B a = Setoid (B a)

module StP (P : MP.Obj) where

  private
    module P = Functor P
    C = op (Preorder po)

  StateFun : Carrier → Setoid ℓ ℓ
  StateFun X =
    ∀[ Store X ]-setoid λ μ →
    ∃[ Carrier ]-setoid λ Y →
      (set→setoid (C [ X , Y ] × Store Y)) ×-setoid P.F₀ Y

  Action : MP.Obj
  Action = ∀[ StateFun ]

open Monad
St : Monad MP
F St = record {
    F₀ = StP.Action
  ; F₁ = {!!}
  ; identity = {!!}
  ; homomorphism = {!!}
  ; F-resp-≡ = {!!} }
η St = {!!}
μ St = {!!}
assoc St = {!!}
identityˡ St = {!!}
identityʳ St = {!!}
