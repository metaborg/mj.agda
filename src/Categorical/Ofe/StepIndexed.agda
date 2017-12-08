module Categorical.Ofe.StepIndexed where

open import Level
open import Data.Maybe hiding (setoid)
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality as PEq using () renaming (refl to ≣-refl; _≡_ to _≣_)

open import Categories.Category
open import Categories.Functor.Core
open import Categories.Support.Equivalence
open import Categories.Support.EqReasoning

open import Categorical.Ofe hiding (_[_≈_])
open import Categorical.Ofe.Cofe
open import Categorical.Ofe.Later
open import Categorical.Ofe.Predicates
open import Categorical.ISetoids.Equality

open Category
open Functor
open Setoid

-- We are using the Category library's definition of setoids (with an irrelevant equivalence)
MaybeS : ∀ {s₁ s₂} → Setoid s₁ s₂ → Setoid _ _
Carrier (MaybeS A) = Maybe (Carrier A)
_≈_ (MaybeS A) = Eq (_≈_ A)
isEquivalence (MaybeS A) = Eq-isEquivalence (isEquivalence A)

module StepIndexed {ℓ ℓ'}(A : Setoid ℓ ℓ') where
  -- fueled monotone functions with strong bi-similarity

  record ⇀_ : Set (ℓ ⊔ ℓ') where
    infixl 100 _⟨_⟩
    field
      _⟨_⟩ : ℕ → Maybe (Carrier A)
      . _⟨0⟩ : MaybeS A [ _⟨_⟩ 0 ≈ nothing ]
      .monotone : ∀ {m n x} → m ≤ n →
                  (MaybeS A) [ _⟨_⟩ m ≈ just x ] → (MaybeS A) [ _⟨_⟩ n ≈ just x ]

  open ⇀_ public

  ⇀-setoid : Setoid _ _
  Carrier ⇀-setoid = ⇀_
  _≈_ ⇀-setoid a b = ∀ n → (MaybeS A) [ a ⟨ n ⟩ ≈ b ⟨ n ⟩ ]
  isEquivalence ⇀-setoid = record
    { refl = λ n → MA.refl
    ; sym = λ p n → MA.sym (p n)
    ; trans = λ p q n → MA.trans (p n) (q n) }
    where module MA = Setoid (MaybeS A)

  open Ofe
  infixl 1000 ⇀-ofe_
  ⇀-ofe_ : Ofe _ _ _
  setoid ⇀-ofe_ = ⇀-setoid
  _≈⟨_⟩_ ⇀-ofe_ f n g = ∀ {m} → m ≤ n → (MaybeS A) [ f ⟨ m ⟩ ≈ g ⟨ m ⟩ ]
  equiv ⇀-ofe_ = record
    { refl = λ m≤n → MA.refl
    ; sym = λ p m≤n → MA.sym (p m≤n)
    ; trans = λ p q m≤n → MA.trans (p m≤n) (q m≤n) }
    where module MA = Setoid (MaybeS A)
  limit₁ ⇀-ofe_ = λ p n m≤n → p _
  limit₂ ⇀-ofe_ = λ p n → p n (≤-reflexive ≣-refl)
  monotone ⇀-ofe_ {x = f}{g} n≥n' eqₙ m≤n = eqₙ (≤-trans m≤n n≥n')

  inhabited : ⇀_
  _⟨_⟩ inhabited x = nothing
  _⟨0⟩ inhabited = nothing
  monotone inhabited _ ()

  open Cofe
  ⇀-cofe_ : Cofe _ _ _
  ofe  ⇀-cofe_ = ⇀-ofe_
  conv ⇀-cofe_ c = lim
    -- the limit is the diagonal of the chain
    (record
      { _⟨_⟩ = λ n → (c at n) ⟨ n ⟩
      ; _⟨0⟩ = (c at 0) ⟨0⟩
      ; monotone = λ {m}{n}{x} m≤n eq →
        let module M = Setoid (MaybeS A) in
        monotone
          (c at n)
          m≤n
          (M.trans (cauchy c m≤n (≤-reflexive ≣-refl) (≤-reflexive ≣-refl)) eq)
      })
    (λ n {m} m≤n → cauchy c m≤n (≤-reflexive ≣-refl) (≤-reflexive ≣-refl))

open StepIndexed using (_⟨_⟩; monotone; _⟨0⟩; ⇀-cofe_)
                 renaming (⇀-ofe_ to ⇀_; inhabited to ⇀-inhabited) public

import Categories.Support.SetoidFunctions as SF
fuel : ∀ {e}{A B : Setoid e e} → (f : A SF.⟶ B) → Ofes [ Δ A , ⇀ B ]
_⟨$⟩_ (fuel f) a = record
  { _⟨_⟩ = λ where
     ℕ.zero → nothing
     (ℕ.suc x) → just (f SF.⟨$⟩ a)
  ; _⟨0⟩ = nothing
  ; monotone = λ where
     z≤n ()
     (s≤s m≤n) eq → eq }
cong (fuel f) eq z≤n = nothing
cong (fuel f) eq (s≤s m≤n) = just (SF.cong f eq)

-- subtract 1 fuel
↘ : ∀ {e e'}{A : Setoid e e'} → Ofes [ ⇀ A ,  ⇀ A ]
_⟨$⟩_ ↘ f = record
  { _⟨_⟩ = λ n → f ⟨ n ∸ 1 ⟩
  ; _⟨0⟩ = f ⟨0⟩
  ; monotone = λ {m n} m≤n eq → monotone f (∸-mono {u = 1}{v = 1} m≤n (≤-reflexive ≣-refl)) eq }
  where open Data.Nat.Properties
cong ↘ x≈y {m} m≤n = x≈y (≤-trans (n∸m≤n 1 m) m≤n)

.↘-contractive : ∀ {e e'}{A : Setoid e e'} → Contractive (↘ {A = A})
↘-contractive {A = A} {f}{g} Later.now z≤n = M.trans (f ⟨0⟩) (M.sym (g ⟨0⟩))
  where module M = Setoid (MaybeS A)
↘-contractive (Later.next x≈y) m≤n = x≈y (∸-mono {u = 1}{v = 1} m≤n (≤-reflexive ≣-refl))
