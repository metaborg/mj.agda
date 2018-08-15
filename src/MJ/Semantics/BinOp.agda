import MJ.Classtable.Core as Core

module MJ.Semantics.BinOp {c}(Ct : Core.Classtable c) where

open import Prelude hiding (Bool)
open import Data.Sum
open import Data.Bool as Bool
open import Data.Integer as Int
open import Relation.Nullary.Decidable

open import MJ.Syntax.BinOp Ct
open import MJ.Semantics.Values Ct

eval-bop : ∀ {Σ a b c} → BinOp a b c → Val Σ a → Val Σ b → Val Σ c
eval-bop (== (inj₁ x)) l r = bool (l ≟val⟨ x ⟩ r)
eval-bop (== (inj₂ x)) l r = bool (r ≟val⟨ x ⟩ l)
eval-bop (!= (inj₁ x)) l r = bool (not (l ≟val⟨ x ⟩ r))
eval-bop (!= (inj₂ x)) l r = bool (not (r ≟val⟨ x ⟩ l))
eval-bop < (num x) (num y) = bool ⌊ Int.suc x Int.≤? y ⌋
eval-bop <= (num x) (num y) = bool ⌊ x Int.≤? y ⌋
eval-bop > (num x) (num y) = bool ⌊ Int.suc y Int.≤? x ⌋
eval-bop >= (num x) (num y) = bool ⌊ y Int.≤? x ⌋
eval-bop + (num x) (num y) = num (x Int.+ y)
eval-bop - (num x) (num y) = num (x Int.- y)
eval-bop * (num x) (num y) = num (x Int.* y)
eval-bop orb (bool x) (bool y) = bool (x Bool.∨ y)
eval-bop xorb (bool x) (bool y) = bool (x Bool.xor y)
eval-bop andb (bool x) (bool y) = bool (x Bool.∧ y)
