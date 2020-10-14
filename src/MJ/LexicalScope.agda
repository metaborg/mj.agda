open import Prelude
open import MJ.Classtable.Core

module MJ.LexicalScope c where

open import Data.List
open import Data.List.Membership.Propositional
open import MJ.Types

Ctx : Set
Ctx = List (Ty c)

Var : Ctx → Ty c → Set
Var Γ a = a ∈ Γ

_+local_ : Ctx → Ty c → Ctx
_+local_ Γ a = a ∷ Γ
