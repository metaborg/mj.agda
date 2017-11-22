module Categorical.Functor.Const where

open import Categories.Category
open import Categories.Functor using (Functor)

const : ∀ {o ℓ e o' ℓ' e'}{D : Category o' ℓ' e'}{C : Category o ℓ e} → Category.Obj D → Functor C D
const {D = D} o = record
  { F₀ = λ _ → o
  ; F₁ = λ _ → Category.id D
  ; identity = refl
  ; homomorphism = λ {X} {Y} {Z} {f} {g} → sym (Category.identityˡ D)
  ; F-resp-≡ = λ x → refl
  }
  where open Category.Equiv D
