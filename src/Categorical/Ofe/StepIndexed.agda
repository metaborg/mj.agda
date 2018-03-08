module Categorical.Ofe.StepIndexed where

open import Level
open import Relation.Nullary
open import Data.Empty
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
open import Categorical.ISetoids.Monads.Maybe

open Category
open Functor
open Setoid

module StepIndexed {ℓ ℓ'}(A : Setoid ℓ ℓ') where
  -- fueled monotone functions with strong bi-similarity

  record ⇀_ : Set (ℓ ⊔ ℓ') where
    infixl 100 _⟨_⟩
    field
      _⟨_⟩   : ℕ → Maybe (Carrier A)
      . _⟨0⟩ : Maybe-setoid A [ _⟨_⟩ 0 ≈ nothing ]
      .monotone : ∀ {m n x} → m ≤ n →
                  (Maybe-setoid A) [ _⟨_⟩ m ≈ just x ] → (Maybe-setoid A) [ _⟨_⟩ n ≈ just x ]

    -- An equivalent formulation of monotone that doesn't require you to know the nth element's exact identity
    .monotone' : ∀ {m n} → m ≤ n → ¬ (Maybe-setoid A) [ _⟨_⟩ m ≈ nothing ] →
                  (Maybe-setoid A) [ _⟨_⟩ n ≈ _⟨_⟩ m ]
    monotone' {m}{n} m≤n neq with _⟨_⟩ m | PEq.inspect _⟨_⟩ m
    ... | nothing | _ = ⊥-elim (neq nothing)
    ... | just z | PEq.[ eq ] = monotone m≤n (reflexive (Maybe-setoid A) eq)

  open ⇀_ public

  ⇀-setoid : Setoid _ _
  Carrier ⇀-setoid = ⇀_
  _≈_ ⇀-setoid a b = ∀ n → (Maybe-setoid A) [ a ⟨ n ⟩ ≈ b ⟨ n ⟩ ]
  isEquivalence ⇀-setoid = record
    { refl = λ n → MA.refl
    ; sym = λ p n → MA.sym (p n)
    ; trans = λ p q n → MA.trans (p n) (q n) }
    where module MA = Setoid (Maybe-setoid A)

  open Ofe
  infixl 1000 ⇀-ofe_
  ⇀-ofe_ : Ofe _ _ _
  setoid ⇀-ofe_ = ⇀-setoid
  _≈⟨_⟩_ ⇀-ofe_ f n g = ∀ {m} → m ≤ n → (Maybe-setoid A) [ f ⟨ m ⟩ ≈ g ⟨ m ⟩ ]
  equiv ⇀-ofe_ = record
    { refl = λ m≤n → MA.refl
    ; sym = λ p m≤n → MA.sym (p m≤n)
    ; trans = λ p q m≤n → MA.trans (p m≤n) (q m≤n) }
    where module MA = Setoid (Maybe-setoid A)
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
        let module M = Setoid (Maybe-setoid A) in
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
  where module M = Setoid (Maybe-setoid A)
↘-contractive (Later.next x≈y) m≤n = x≈y (∸-mono {u = 1}{v = 1} m≤n (≤-reflexive ≣-refl))

-- it is a functor between ISetoids and Ofe
open import Categories.Agda
private
  module Functorial {s₁ s₂} where
    ISets = ISetoids s₁ s₂
    module ISets = Category ISets

    module Maybe-functor = Functor (Maybe-functor {s₁}{s₂})

    hmap : ∀ {A B} → ISets [ A , B ] → Ofes [ ⇀ A , ⇀ B ]
    _⟨$⟩_ (hmap {A}{B} f) x = record
      { _⟨_⟩ = λ n → (Maybe-functor.F₁ f) SF.⟨$⟩ (x ⟨ n ⟩)
      ; _⟨0⟩ =
        let open SetoidReasoning (Maybe-setoid B) in
        begin
          Maybe-functor.F₁ f SF.⟨$⟩ (x ⟨ 0 ⟩)
        ↓⟨ SF.cong (Maybe-functor.F₁ f) (x ⟨0⟩) ⟩
          Maybe-functor.F₁ f SF.⟨$⟩ nothing
        ↓⟨ nothing ⟩
          nothing
        ∎
      ; monotone = λ {m}{n}{y} m≤n eq →
        let open SetoidReasoning (Maybe-setoid B) in
        begin
          Maybe-functor.F₁ f SF.⟨$⟩ x ⟨ n ⟩
        ↓⟨ SF.cong (Maybe-functor.F₁ f) (StepIndexed.monotone' x m≤n (F₁-just f eq)) ⟩
          Maybe-functor.F₁ f SF.⟨$⟩ x ⟨ m ⟩
        ↓⟨ eq ⟩
          just y
        ∎
      }
    cong  (hmap f) xeq m≤n = SF.cong (Maybe-functor.F₁ f) (xeq m≤n)

    .ident : ∀ {X}(x y : StepIndexed.⇀ X){n m} → (⇀ X) [ x ≈⟨ n ⟩ y ] → m ≤ n →
             (Maybe-setoid X) [ (Maybe-functor.F₁ (ISets.id {X})) SF.⟨$⟩ x ⟨ m ⟩ ≈ y ⟨ m ⟩ ]
    ident x y xeq m≤n = Maybe-functor.identity (xeq m≤n)

    .hom : ∀ {X Y Z x n y}{f : ISets [ X , Y ]}{g : ISets [ Y , Z ]} → (⇀ X) [ x ≈⟨ n ⟩ y ] →
           ∀ {m} → m ≤ n →
           (Maybe-setoid Z) [
             Maybe-functor.F₁ (ISets [ g ∘ f ]) SF.⟨$⟩ x ⟨ m ⟩ ≈
             (Ofes [ hmap g ∘ hmap f ] ⟨$⟩ y) ⟨ m ⟩ ]
    hom {X}{Z = Z}{x}{n}{y}{f}{g} eq {m} m≤n =
      begin
        Maybe-functor.F₁ (ISets [ g ∘ f ]) SF.⟨$⟩ x ⟨ m ⟩
      ↓⟨ SF.cong (Maybe-functor.F₁ (ISets [ g ∘ f ])) (eq m≤n) ⟩
        Maybe-functor.F₁ (ISets [ g ∘ f ]) SF.⟨$⟩ y ⟨ m ⟩
      ↓⟨ Maybe-functor.homomorphism (refl (Maybe-setoid X) {x = y ⟨ m ⟩}) ⟩
        (Ofes [ hmap g ∘ hmap f ] ⟨$⟩ y) ⟨ m ⟩
      ∎
      where open SetoidReasoning (Maybe-setoid Z)

    .resp : ∀ {A B}{F G : ISets [ A , B ]} → ISets [ F ≡ G ] → Ofes [ hmap F ≡ hmap G ]
    resp F≡G x≈y m≤n = Maybe-functor.F-resp-≡ F≡G (x≈y m≤n)

⇀-functor : ∀ {o e} → Functor (ISetoids o e) Ofes
F₀ ⇀-functor = ⇀_
F₁ ⇀-functor {A} = Functorial.hmap
identity ⇀-functor {A}{n}{x}{y} xeq m≤n = Functorial.ident x y xeq m≤n
homomorphism ⇀-functor {X}{Y}{Z}{f}{g}{n}{x}{y} eq = Functorial.hom {x = x}{n}{y} eq
F-resp-≡ ⇀-functor = Functorial.resp

module ⇀-functor {o e} = Functor (⇀-functor {o}{e})
