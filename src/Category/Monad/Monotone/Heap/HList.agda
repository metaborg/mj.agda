import Relation.Unary.Monotone as Mono

open import Data.List.Prefix
open import Data.List as List

module Category.Monad.Monotone.Heap.HList
  (T : Set)
  (V : T → List T → Set)⦃ wkV : ∀ {a} → Mono.Monotone ⊑-preorder (V a) ⦄ where

open import Level
open import Data.List.All as All
open import Data.List.All.Properties.Extra
open import Data.List.Any
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Properties.Extra
open import Data.Product
open import Data.Unit

open import Relation.Binary using (Preorder)
open import Relation.Unary hiding (_∈_)
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Unary.Monotone.Prefix {T = T}

private
  HeapT : Set
  HeapT = List T

  Heap : Pred HeapT _
  Heap = λ W → All (λ a → V a W) W

open Mono (⊑-preorder {A = T})
open import Category.Monad.Monotone (⊑-preorder {A = T})
open import Category.Monad.Monotone.State ⊑-preorder Heap
open import Category.Monad.Monotone.Heap ⊑-preorder T V Heap _∈_
open import Category.Monad using (RawMonad)

module _ {M : Set → Set}⦃ Mon : RawMonad M ⦄ where
  private module M = RawMonad Mon

  hlist-heap-monad : HeapMonad (MST M)
  HeapMonad.store hlist-heap-monad {a}{i} sv μ =
    let ext = ∷ʳ-⊒ a i in M.return (_ , ext , (wk ext μ all-∷ʳ wk ext sv) , ∈-∷ʳ i a )
  HeapMonad.modify hlist-heap-monad ptr v μ =
    M.return (_ , ⊑-refl , μ All[ ptr ]≔' v , lift tt)
  HeapMonad.deref hlist-heap-monad ptr μ =
    M.return (_ , ⊑-refl , μ , ∈-all ptr μ)
