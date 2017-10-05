open import Agda.Primitive
open import Data.List.Most
open import Data.List.All as List∀
open import Function
open import Level

module Common.Weakening  where

{-
  We define a class of weakenable (or monotone) predicates over
  lists.

  To this end, we define a `Weakenable` record parameterized over such
  predicates.  We can make the definitions of `Weakenable` available
  using the syntax:

  open Weakenable ⦃...⦄ public

  Whenever we use `wk e p` where `p : P x` and `x : X` somewhere, Agda
  will use instance argument search to find an instance (witness :
  Weakenable {X} P).  See also
  http://agda.readthedocs.io/en/v2.5.3/language/instance-arguments.html
-}

record Weakenable {i j}{A : Set i}(p : List A → Set j) : Set (i ⊔ j) where
  field wk : ∀ {w w'} → w ⊑ w' → p w → p w'

{-
  The notion of `Weakenable` above is not the most general: in
  general, weakenable predicates can be defined over *any* preorder.
  See `Experiments.Category` for a more general definition and
  treatment.

  For the purposes of developing the interpreters presented in our
  paper, however, the definition of `Weakenable` above is useful
  indeed.
-}

open Weakenable ⦃...⦄ public

{-
  We define a few derived instances of Weakenable that appear
  commonly.
-}

instance
  any-weakenable : ∀ {i}{A : Set i}{x : A} → Weakenable (λ xs → x ∈ xs)
  any-weakenable = record { wk = λ ext l → ∈-⊒ l ext }

  all-weakenable : ∀ {i}{A : Set i}{j}{B : Set j}{xs : List B}
                     {k}{C : B → List A → Set k}( wₐ : ∀ x → Weakenable (C x) ) →
                     Weakenable (λ ys → All (λ x → C x ys) xs)
  all-weakenable wₐ = record {
    wk = λ ext v → List∀.map (λ {a} y → Weakenable.wk (wₐ a) ext y) v }

  const-weakenable : ∀ {j i}{I : Set i}{A : Set j} → Weakenable {A = I} (λ _ → A)
  const-weakenable = record { wk = λ ext c → c }

-- nicer syntax for transitivity of prefixes
infixl 30 _⊚_
_⊚_ : ∀ {i}{A : Set i}{W W' W'' : List A} → W' ⊒ W → W'' ⊒ W' → W'' ⊒ W
_⊚_ co₁ co₂ = ⊑-trans co₁ co₂

{-
  Another common construction is that of products of weakenable
  predicates.  In the paper this is redefined; but we just alias the
  Agda standard library version here and prove that it is indeed a
  member of the Weakenable typeclass.
-}
open import Relation.Unary
open import Data.Product
_⊗_ : ∀ {a}{i j}{W : Set a}(p : W → Set i)(q : W → Set j)(w : W) → Set (i ⊔ j)
_⊗_ = _∩_

instance
  weaken-pair : ∀ {a}{A : Set a}{i j}{p : List A → Set i}{q : List A → Set j}
                  ⦃ wp : Weakenable p ⦄ ⦃ wq : Weakenable q ⦄ →
                  Weakenable (p ⊗ q)
  weaken-pair = record { wk = λ{ ext (x , y) → (wk ext x , wk ext y) } }
