open import MJ.Types as Types
import MJ.Classtable.Core as Core

module MJ.Semantics.Values {c}(Ct : Core.Classtable c) where

open import Prelude

open import Level renaming (suc to lsuc; zero to lzero)
open import Data.List as List hiding (null)
open import Data.Vec hiding (_∈_)
open import Data.List.Any.Membership.Propositional
open import Data.List.All as List∀
open import Data.List.All.Properties.Extra as List∀++
open import Data.List.Prefix
open import Data.Vec.All as Vec∀ using ()


open Core c
open Classtable Ct
open import MJ.Classtable.Membership Ct
open import MJ.LexicalScope Ct
open import Common.Weakening

open Weakenable ⦃...⦄

data Val (W : World c) : Ty c → Set where
  num  : ℕ → Val W int
  unit : Val W void
  null : ∀ {C} → Val W (ref C)
  ref  : ∀ {C P} → (obj C) ∈ W → Σ ⊢ C <: P → Val W (ref P)

default : ∀ {W} → (a : Ty c) → Val W a
default void = unit
default int = num 0
default (ref x) = null

--
-- environments as indirections into a heap
--

Env : ∀ (Γ : Ctx)(W : World c) → Set
Env Γ W = All (λ a → vty a ∈ W) Γ

_⊕_ : ∀ {Γ W a} → Env Γ W → (vty a) ∈ W → Env (Γ +local a) W
_⊕_ E v = v ∷ E

open import Data.List.Any
getvar : ∀ {Γ W a} → Var Γ a → Env Γ W → vty a ∈ W
getvar px E = ∈-all px E

--
-- Abstract object encoding
--

record ObjEncoding : Set (lsuc lzero) where
  field
    Obj : World c → Cid c → Set
    weaken-obj : ∀ {W W'} cid → W' ⊒ W → Obj W cid → Obj W' cid
    getter : ∀ {W m a} c → Obj W c → IsMember c FIELD m a → Val W a
    setter : ∀ {W m a} c → Obj W c → IsMember c FIELD m a → Val W a → Obj W c
    defaultObject : ∀ {W} c → Obj W c

  data StoreVal (W : World c) : Ty⁺ c → Set where
    val : ∀ {ty} → Val W ty → StoreVal W (vty ty)
    obj : ∀ cid → Obj W cid → StoreVal W (obj cid)

  Store : World c → Set
  Store W = All (StoreVal W) W

--
-- weakening
--

weaken-val : ∀ {a}{W W' : World c} → W ⊒ W' → Val W' a → Val W a
weaken-val ext (num n) = num n
weaken-val ext unit = unit
weaken-val ext null = null
weaken-val ext (ref x sub) = ref (∈-⊒ x ext) sub

instance

  val-weakenable : ∀ {a} → Weakenable (λ W → Val W a)
  val-weakenable = record { wk = weaken-val }

  list-weakenable : ∀ {a}{A : World c → Set a}⦃ wₐ : Weakenable A ⦄ → Weakenable (λ W → List (A W))
  list-weakenable ⦃ wₐ ⦄ = record {wk = λ ext v → List.map (wk ext) v }

  list∀-weakenable : ∀ {b}{B : Set b}{xs : List B}
                     {a}{A : B → World c → Set a}⦃ wₐ : ∀ x → Weakenable (A x) ⦄ →
                     Weakenable (λ W → All (λ x → A x W) xs)
  list∀-weakenable ⦃ wₐ ⦄ = record { wk = λ ext v → List∀.map (λ y → wk ⦃ wₐ _ ⦄ ext y) v }

