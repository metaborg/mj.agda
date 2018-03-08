open import Prelude hiding (begin_; _∎; _≡⟨_⟩_)

module MJ.Classtable.Core (c : ℕ) where

open import Data.List
open import Data.List.Any.Membership.Propositional
open import Relation.Binary.Core using (Transitive)
open import Data.Vec hiding (_∈_)
open import Data.Maybe
open import Data.String

open import Relation.Binary using (Decidable)
open import Relation.Binary.Product.Pointwise using (_×-≟_)
open import Relation.Binary.List.Pointwise using (decidable-≡)

open import MJ.Types as Types

{-
To model that a class may define both field and methods in a uniform manner, we
choose to introduce two namespaces.
-}
data NS : Set where
  METHOD : NS
  FIELD  : NS

typing : NS → Set
typing METHOD = Sig c
typing FIELD = Ty c

-- decidable equality on typings
_typing-≟_ : ∀ {ns} → Decidable (_≡_ {A = typing ns})
_typing-≟_ {METHOD} = (decidable-≡ Types._≟_) ×-≟ Types._≟_
_typing-≟_ {FIELD}  = Types._≟_

{-
We choose to make parent declarations obligatory and have a distinguished class
identifier Object in which inheritance chains find their foundation.

The field constr of this record provides access to the constructor parameter types.

The field decls returns a list of named members for each namespace, where the
type of the member is namespace-dependent. The uniformity of member definitions
permits a notion of membership that works for both fields and methods:
-}

Decl : NS → Set
Decl ns = String × typing ns

record Class : Set where
  constructor class
  field
    parent  : Cid c
    constr  : List (Ty c) -- argument types
    decls   : (ns : NS) → List (Decl ns)

ObjectClass = class Object [] (λ _ → [])

{-
Conceptually a class table stores the types of all members of all classes.
It is modeled by a total function from class identifiers to instances of
a record Class.
-}
PreClasstable = Cid c → Class

{-
We can define inheritance as the transitive closure of a step relation
between class identifiers under a given classtable Σ:
-}
data _⊢_<:ₛ_ (Σ : PreClasstable) : Cid c → Cid c → Set where
  super : ∀ {cid} → Σ ⊢ cls cid <:ₛ (Class.parent (Σ (cls cid)))

open import Data.Star
_⊢_<:_ : (Σ : PreClasstable)(cid : Cid c) → (pid : Cid c) → Set
_⊢_<:_ Σ = Star (_⊢_<:ₛ_ Σ)

{-
We'll restrict classtables to those that satisfy three properties:

- founded: says that Object is at the base of sub-typing
- rooted: says that every class inherits from Object
- Σ-object: gives meaning to the distinguished Object class identifier
-}
record Classtable : Set where
  field
    Σ        : PreClasstable
    founded  : Class.parent (Σ Object) ≡ Object
    rooted   : ∀ C → Σ ⊢ C <: Object
    Σ-Object : Σ Object ≡ ObjectClass

  _<∶_ : ∀ (cid pid : Cid c) → Set
  a <∶ b = Σ ⊢ a <: b

  -- extended inheritance relation that is defined on all types
  data _<:<_ : (a b : Ty c) → Set where
    int  : int <:< int
    bool : bool <:< bool
    void : void <:< void
    cls  : ∀ {a b} → _<∶_ a b → ref a <:< ref b

  open import Relation.Binary
  open import Data.Nat.Properties

  {-
  We can show that the subtyping relation is indeed reflexive and transitive
  -}
  <:-reflexive  : Reflexive (_⊢_<:_ Σ)
  <:-reflexive  = ε

  <:-transitive : Transitive (_⊢_<:_ Σ)
  <:-transitive = _◅◅_

  {-
  From the axioms of the classtable we can derive the important properties
  that cyclic inheritance is impossible and that consequently inheritance
  proofs are unique.

  The proof is slightly involved because we have to make sure that Agda
  believes that it is total.
  -}
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

    -- generate an inheritance proof of arbitrary length,
    -- given an inheritance proof from a parent to a child
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

  -- Proves that a parent can't inherit from it's children,
  Σ-acyclic : ∀ c → ¬ Σ ⊢ Class.parent (Σ (cls c)) <: (cls c)
  Σ-acyclic c px with lem-inf c px (len $ rooted (cls c))
  ... | qx , impossible with lem-len qx (rooted (cls c))
  ... | z = ⊥-elim (<⇒≱ impossible z)

  -- Trivially we have that Object cannot inherit from any class
  ¬Object<:x : ∀ {cid} → ¬ Σ ⊢ Object <: cls cid
  ¬Object<:x (() ◅ p)

  -- Using acyclicity we can show that inheritance proofs are unique
  <:-unique : ∀ {c p} → (l r : Σ ⊢ c <: p) → l ≡ r
  <:-unique ε ε = refl
  <:-unique ε ch@(super ◅ r) = ⊥-elim (Σ-acyclic _ r)
  <:-unique ch@(super ◅ l) ε = ⊥-elim (Σ-acyclic _ l)
  <:-unique (super ◅ l) (super ◅ r) with <:-unique l r
  ... | refl = refl
