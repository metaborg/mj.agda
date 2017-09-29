open import Prelude hiding (begin_; _∎; _≡⟨_⟩_)

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

    len-◅◅ : ∀ {c p p'}(s : Σ ⊢ c <: p)(s' : Σ ⊢ p <: p') → len (s ◅◅ s') ≡ len s + len s'
    len-◅◅ ε _ = refl
    len-◅◅ (x ◅ s) s' rewrite len-◅◅ s s' = refl

    lem-len : ∀ {c p}(px : Σ ⊢ c <: p)(qx : Σ ⊢ c <: Object) → len px ≤ len qx
    lem-len ε ε = z≤n
    lem-len ε (x ◅ qx) = z≤n
    lem-len (() ◅ px) ε
    lem-len (super ◅ px) (super ◅ qx) = s≤s (lem-len px qx)

    open ≤-Reasoning

    -- modulo termination checking trickery this lemma is provable;
    -- we can do this using wellfounded induction on the gap between the lengths.
    -- which is strictly decreasing in size
    lem-inf : ∀ c → Σ ⊢ Class.parent (Σ (cls c)) <: (cls c) → ∀ n → ∃ λ (px : Σ ⊢ (cls c) <: (cls c)) → len px > n
    lem-inf c px n with helper px n
      where
        helper : (p : Σ ⊢ Class.parent (Σ (cls c)) <: (cls c)) → ∀ gap → ∃ λ (px : Σ ⊢ (cls c) <: (cls c)) → len px ≥ gap + len p
        helper p zero = (super ◅ p) , ≤-step ≤-refl
        helper p (suc gap) with gap ≤? len p
        ... | yes q = (super ◅ p ◅◅ (super ◅ p)) , s≤s (begin
            (gap + len p)
              ≤⟨ +-mono-≤ q (≤-step ≤-refl) ⟩
            len p + (suc (len p))
              ≡⟨ sym (len-◅◅ p (super ◅ p)) ⟩
            len (p ◅◅ super ◅ p)
          ∎)
        ... | no ¬q with helper (p ◅◅ (super ◅ p)) gap
        ... | z , q = z , (begin
            suc (gap + len p)
              ≡⟨ sym $ m+1+n≡1+m+n gap (len p) ⟩
            gap + (len (super ◅ p))
              ≤⟨ +-mono-≤ { gap } ≤-refl (≤-steps (len p) ≤-refl) ⟩
            gap + (len p + len (super ◅ p))
              ≡⟨ cong (_+_ gap) (sym $ len-◅◅ p (super ◅ p)) ⟩
            gap + (len (p ◅◅ (super ◅ p)))
              ≤⟨ q ⟩
            len z ∎)
          where open import Data.Nat.Properties.Extra
    ... | py , z = super ◅ px ◅◅ py , s≤s (subst (_≤_ n) (sym $ len-◅◅ px py) (≤-steps (len px) (m+n≤o⇒m≤o n z)))

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
