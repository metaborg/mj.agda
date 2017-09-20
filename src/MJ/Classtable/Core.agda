open import Prelude

module MJ.Classtable.Core (c : ℕ) where

open import Data.List
open import Data.List.Any.Membership.Propositional
open import Relation.Binary.Core using (Transitive)
open import Data.Vec hiding (_∈_)
open import Data.Maybe
open import Data.String

open import MJ.Types as Types

data NS : Set where
  METHOD : NS
  FIELD  : NS

typing : NS → Set
typing METHOD = Sig c
typing FIELD = Ty c

open import Relation.Binary using (Decidable)
open import Relation.Binary.Product.Pointwise using (_×-≟_)
open import Relation.Binary.List.Pointwise using (decidable-≡)

-- decidable equality on typings
_typing-≟_ : ∀ {ns} → Decidable (_≡_ {A = typing ns})
_typing-≟_ {METHOD} = (decidable-≡ Types._≟_) ×-≟ Types._≟_
_typing-≟_ {FIELD}  = Types._≟_

record Class : Set where
  constructor class
  field
    parent  : Cid c
    constr  : List (Ty c) -- argument types
    decls   : (ns : NS) → List (String × typing ns)

ObjectClass = class Object [] (λ _ → [])

PreClasstable = Cid c → Class

data _⊢_<:ₛ_ (Σ : PreClasstable) : Cid c → Cid c → Set where
  super : ∀ {cid} → Σ ⊢ cls cid <:ₛ (Class.parent (Σ (cls cid)))

open import Data.Star
_⊢_<:_ : (Σ : PreClasstable)(cid : Cid c) → (pid : Cid c) → Set
_⊢_<:_ Σ = Star (_⊢_<:ₛ_ Σ)

record Classtable : Set where
  field
    Σ        : PreClasstable
    founded  : Class.parent (Σ Object) ≡ Object
    rooted   : ∀ C → Σ ⊢ C <: Object
    Σ-Object : Σ Object ≡ ObjectClass

  _<∶_ : ∀ (cid pid : Cid c) → Set
  a <∶ b = Σ ⊢ a <: b

  open import Relation.Binary
  open import Data.Nat.Properties

  <:-reflexive  : Reflexive (_⊢_<:_ Σ)
  <:-reflexive  = ε

  <:-transitive : Transitive (_⊢_<:_ Σ)
  <:-transitive = _◅◅_

  private
    len : ∀ {c p} → Σ ⊢ c <: p → ℕ
    len ε = 0
    len (x ◅ px) = suc $ len px

    lem-len : ∀ {c p}(px : Σ ⊢ c <: p)(qx : Σ ⊢ c <: Object) → len px ≤ len qx
    lem-len ε ε = z≤n
    lem-len ε (x ◅ qx) = z≤n
    lem-len (() ◅ px) ε
    lem-len (super ◅ px) (super ◅ qx) = s≤s (lem-len px qx)

    -- modulo termination checking trickery this lemma is provable;
    -- we can do this using wellfounded induction on the gap between the lengths.
    -- which is strictly decreasing in size
    postulate lem-inf : ∀ c → Σ ⊢ Class.parent (Σ (cls c)) <: (cls c) → ∀ n → ∃ λ (px : Σ ⊢ (cls c) <: (cls c)) → len px > n
    {-}
    lem-inf _ px n with n ≤? len (px ◅◅ (super ◅ px))
    lem-inf c₁ px n | yes p = super ◅ px ◅◅ (super ◅ px) , s≤s p
    lem-inf c₁ px n | no ¬p = {!!}
    -}

  Σ-acyclic : ∀ c → ¬ Σ ⊢ Class.parent (Σ (cls c)) <: (cls c)
  Σ-acyclic c px with lem-inf c px (len $ rooted (cls c))
  ... | qx , impossible with lem-len qx (rooted (cls c))
  ... | z = ⊥-elim (<⇒≱ impossible z)

  ¬Object<:x : ∀ {cid} → ¬ Σ ⊢ Object <: cls cid
  ¬Object<:x (() ◅ p)

  <:-unique : ∀ {c p} → (l r : Σ ⊢ c <: p) → l ≡ r
  <:-unique ε ε = refl
  <:-unique ε ch@(super ◅ r) = ⊥-elim (Σ-acyclic _ r)
  <:-unique ch@(super ◅ l) ε = ⊥-elim (Σ-acyclic _ l)
  <:-unique (super ◅ l) (super ◅ r) with <:-unique l r
  ... | refl = refl
