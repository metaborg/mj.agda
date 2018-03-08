open import MJ.Types
import MJ.Classtable.Core as Core
import MJ.Classtable.Code as Code
import MJ.Syntax as Syntax

module MJ.Semantics.Objects.Flat {c}(Ct : Core.Classtable c) where

open import Prelude

open import Level renaming (suc to lsuc; zero to lzero)
open import Data.Vec hiding (_++_; lookup; drop)
open import Data.Star
open import Data.List
open import Data.List.First.Properties
open import Data.List.Any.Membership.Propositional
open import Data.List.Any.Properties
open import Data.List.All as List∀
open import Data.List.All.Properties.Extra
open import Data.List.Prefix
open import Data.List.Properties.Extra
open import Data.Maybe as Maybe hiding (All; map)
open import Data.Maybe.All as MayAll using ()
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality

open import MJ.Semantics.Values Ct
open import MJ.Semantics.Objects Ct
open import MJ.Syntax Ct
open Core c
open Classtable Ct
open import MJ.Classtable.Membership Ct

private

  collect : ∀ {cid}(chain : Σ ⊢ cid <: Object) ns → List (String × typing ns)
  collect (super {cid} ◅ ch) ns = Class.decls (Σ (cls cid)) ns ++ collect ch ns
  collect ε ns = Class.decls (Σ Object) ns

  {-
  We define collect members by delegation to collection of members over a particular
  inheritance chain.
  This makes the definition structurally recursive and is sound by the fact that
  inheritance chains are unique.
  -}
  collect-members : ∀ cid ns → List (String × typing ns)
  collect-members cid ns = collect (rooted cid) ns

  {-
  An Object is then simply represented by a list of values for all it's members.
  -}
  Obj : (World c) → (cid : _) → Set
  Obj W cid = All (λ d → Val W (proj₂ d)) (collect-members cid FIELD)

  weaken-obj : ∀ {W W'} cid → W' ⊒ W → Obj W cid → Obj W' cid
  weaken-obj cid ext O = List∀.map (weaken-val ext) O

  {-
  We can relate the flat Object structure with the hierarchical notion of membership
  through the definition of `collect`.
  This allows us to get and set members on Objects.
  -}
  getter : ∀ {W n a} cid → Obj W cid → IsMember cid FIELD n a → Val W a
  getter cid O q with rooted cid
  getter .Object O (.Object , ε , def) | ε = ∈-all (proj₁ (first⟶∈ def)) O
  getter .Object O (_ , () ◅ _ , _) | ε
  getter ._ O (._ , ε , def) | super {cid} ◅ z
    with split-++ (Class.decls (Σ (cls _)) FIELD) _ O
  ... | own , inherited = ∈-all (proj₁ (first⟶∈ def)) own
  getter ._ O (pid , super {cid} ◅ s , def) | super ◅ z
    with split-++ (Class.decls (Σ (cls _)) FIELD) _ O
  ... | own , inherited rewrite <:-unique z (rooted (Class.parent (Σ (cls cid)))) =
    getter _ inherited (pid , s , def)

  setter : ∀ {W f a} cid → Obj W cid → IsMember cid FIELD f a → Val W a → Obj W cid
  setter (cls cid) O q v with rooted (cls cid)
  setter (cls cid) O (._ , ε , def) v | super ◅ z with split-++ (Class.decls (Σ (cls _)) FIELD) _ O
  ... | own , inherited =
    (own All[ proj₁ (first⟶∈ def) ]≔' v) ++-all inherited
  setter (cls cid) O (._ , super ◅ s , def) v | super ◅ z with split-++ (Class.decls (Σ (cls _)) FIELD) _ O
  ... | own , inherited rewrite <:-unique z (rooted (Class.parent (Σ (cls cid)))) =
    own ++-all setter _ inherited (_ , s , def) v
  setter Object O mem v = ⊥-elim (∉Object mem)

  {-
  A default object instance can be created for every class simply by tabulating `default`
  over the types of all fields of a class.
  -}
  defaultObject' : ∀ {W cid} → (ch : Σ ⊢ cid <: Object) → All (λ d → Val W (proj₂ d)) (collect ch FIELD)
  defaultObject' ε rewrite Σ-Object = []
  defaultObject' {cid = Object} (() ◅ _)
  defaultObject' {cid = cls x} (super ◅ z) =
    List∀.tabulate {xs = Class.decls (Σ (cls x)) FIELD} (λ{ {_ , ty} _ → default ty})
    ++-all
    defaultObject' z

{-
We collect these definitions under the abstract ObjEncoding interface for usage in the semantics
-}
encoding : ObjEncoding
encoding = record {
    Obj = Obj ;
    weaken-obj = λ cid ext O → weaken-obj cid ext O ;
    getter = getter ;
    setter = setter ;
    defaultObject = λ cid → defaultObject' (rooted cid)
  }
