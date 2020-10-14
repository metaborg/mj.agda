import MJ.Classtable.Core as Core


module MJ.Classtable.Membership {c}(Ct : Core.Classtable c) where

open Core c
open Classtable Ct

open import Prelude
open import Data.Star
open import Data.Product hiding (Σ)
open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.Any.Properties
open import Data.List.First.Membership
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Relation.Nullary.Decidable
open import Data.Maybe
open import Data.String as Str
open import Function.Equality using (Π)
open import Function.Inverse using (Inverse)

open import MJ.Types as Types

{-
We can observe that a class declares a member in a particular namespace using a
predicate Declares.
-}
Declares : Cid c → (ns : NS) → String → typing ns → Set
Declares cid ns m ty = let cl = Σ cid in (m , ty) ∈ (Class.decls cl ns)

{-
We define a notion of *declarative membership* of C as the product
of a witness that C inherits from P and a declaration in P.
-}
IsMember : Cid c → (ns : NS) → String → typing ns → Set
IsMember cid ns m ty = let C = Σ cid in ∃ λ P → Σ ⊢ cid <: P × Declares P ns m ty

{-
We can prove that Object has no members.
-}
∉Object : ∀ {ns m a} → ¬ IsMember Object ns m a
∉Object (.Object , ε , mem) rewrite Σ-Object = ¬x∈[] mem
∉Object (._ , () ◅ _ , _)

{-
And we can show that Declares and IsMember are decidable relations
-}
find-declaration : ∀ cid ns n ty → Dec (Declares cid ns n ty)
find-declaration cid ns m ty = find (Str._≟_ ×-≟ _typing-≟_) (m , ty) (Class.decls (Σ cid) ns)

find-member : ∀ cid ns n ty → Dec (IsMember cid ns n ty)
find-member cid ns n ty = helper cid ns n ty (rooted cid)
  where
    helper : ∀ cid ns n ty → Σ ⊢ cid <: Object → Dec (IsMember cid ns n ty)
    helper cid ns n ty ε = no (⊥-elim ∘ ∉Object)
    helper cid ns n ty (super ◅ p) with find-declaration cid ns n ty
    ... | yes q = yes (cid , ε , q)
    ... | no ¬q with helper _ ns n ty p
    ... | yes (pid , s , d) = yes (pid , super ◅ s , d)
    ... | no ¬r = no impossible
      where
        impossible : ¬ (IsMember cid ns n ty)
        impossible (_ , ε , d) = ¬q d
        impossible (pid , Core.super ◅ s , d) = ¬r (pid , s , d)

{-
Using said decision procedures we can formalize a notion of accessible members.
-}
AccMember : Cid c → (ns : NS) → String → typing ns → Set
AccMember cid ns n ty = True (find-member cid ns n ty)

{-
All accessible members are also declarative members, but not vice versa,
because overrides make their super inaccessible.
-}
sound : ∀ {cid ns n ty} → AccMember cid ns n ty → IsMember cid ns n ty
sound p = toWitness p

{-
Declarative members are inherited:
-}
inherit' : ∀ {C P ns m a} → Σ ⊢ C <: P → IsMember P ns m a → IsMember C ns m a
inherit' S (_ , S' , def) = -, S ◅◅ S' , def

{-
Accessible members are inherited (but may point to different definitions thanks to overrides):
-}
inherit : ∀ {m ns ty pid} cid → Σ ⊢ cid <: pid → AccMember pid ns m ty → AccMember cid ns m ty
inherit {m}{ns}{ty} cid s mb with find-member cid ns m ty
... | yes mb' = tt
... | no ¬mb = ⊥-elim (¬mb (inherit' s (sound mb)))
