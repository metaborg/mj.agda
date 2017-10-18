open import MJ.Types as Types
import MJ.Classtable.Core as Core

module MJ.Semantics.Environments {c}(Ct : Core.Classtable c) where

open import Prelude
open import Data.List.Most

open import MJ.LexicalScope c

{-
We equip MJ with mutable lexical environments.
We could choose to model this directly, moving the environment from
the Reader part of the evaluation monad to the State part.

Instead we choose to keep our environments immutable and model
mutability of the values in it by an indirection via the mutable store.
This greatly simplifies the treatment of environments in the interpreter
and keeps the representation lightweight, even though we support block scopes.
-}
Env : ∀ (Γ : Ctx)(W : World c) → Set
Env Γ W = All (λ a → vty a ∈ W) Γ

_⊕_ : ∀ {Γ W a} → Env Γ W → (vty a) ∈ W → Env (Γ +local a) W
_⊕_ E v = v ∷ E

open import Data.List.Any
getvar : ∀ {Γ W a} → Var Γ a → Env Γ W → vty a ∈ W
getvar px E = ∈-all px E
