module Categorical.ISetoids.Monads.Maybe where

open import Level
open import Data.Maybe using (Maybe; Eq; Eq-isEquivalence)
open import Data.Maybe using (just; nothing) public

open import Categories.Category
open import Categories.Agda
open import Categories.Support.Equivalence
open import Categories.Support.SetoidFunctions
open import Categories.Functor.Core

open Setoid
open Functor

_[_maybe≈_] : ∀ {o e}(A : Setoid o e) → (l r : Maybe (Carrier A)) → Set (o ⊔ e)
_[_maybe≈_] A = Eq (_≈_ A)

Maybe-setoid : ∀ {o e} → Setoid o e → Setoid o (o ⊔ e)
Carrier (Maybe-setoid A) = Maybe (Carrier A)
_≈_ (Maybe-setoid A) = _[_maybe≈_] A
isEquivalence (Maybe-setoid A) = Eq-isEquivalence (isEquivalence A)

Maybe-functor : ∀ {o e} → Functor (ISetoids o e) (ISetoids o (o ⊔ e))
F₀ Maybe-functor = Maybe-setoid
_⟨$⟩_ (F₁ Maybe-functor f) nothing  = nothing
_⟨$⟩_ (F₁ Maybe-functor f) (just x) = just (f ⟨$⟩ x)
cong (F₁ Maybe-functor f) (just x≈y) = just (cong f x≈y)
cong (F₁ Maybe-functor f) nothing = nothing
identity Maybe-functor (just x≈y) = just x≈y
identity Maybe-functor nothing = nothing
homomorphism Maybe-functor {f = f}{g} (just x≈y) = just (cong (ISetoids _ _ [ g ∘ f ]) x≈y)
homomorphism Maybe-functor nothing = nothing
F-resp-≡ Maybe-functor feq (just x≈y) = just (feq x≈y)
F-resp-≡ Maybe-functor feq nothing = nothing

open import Data.Product
open import Relation.Nullary

F₁-just : ∀ {o e}{A B : Setoid o e}{x y} → (f : ISetoids _ _ [ A , B ]) → B [ F₁ Maybe-functor f ⟨$⟩ x maybe≈ just y ] →
          ¬ A [ x maybe≈ nothing ]
F₁-just f () nothing

