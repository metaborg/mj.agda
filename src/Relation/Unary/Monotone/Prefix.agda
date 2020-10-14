module Relation.Unary.Monotone.Prefix {ℓ}{T : Set ℓ} where

open import Data.List.Prefix
open import Data.List as List
open import Data.List.Membership.Propositional
open import Data.List.All as All

open import Relation.Unary.Monotone (⊑-preorder {A = T})

instance
  open Monotone

  any-monotone : ∀ {x : T} → Monotone (λ xs → x ∈ xs)
  wk any-monotone ext l = ∈-⊒ l ext
