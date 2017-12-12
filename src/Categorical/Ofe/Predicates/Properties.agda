module Categorical.Ofe.Predicates.Properties where

open import Categories.Category

open import Categorical.Ofe
open import Categorical.Ofe.Predicates
open import Categorical.Ofe.Predicates.Closures
open import Categorical.Ofe.Later

module _ {ℓ} where
  private
    Cat = Ofes {ℓ}{ℓ}{ℓ}

  open Category Cat
  open _⟶_

  ∀-intro : ∀ {X : Set ℓ}{A}{B : Pred X {ℓ}{ℓ}{ℓ}} → (∀ (x : X) → Ofes [ A , B x ]) →
            Ofes [ A , ∀[ X ] B ]
  _⟨$⟩_ (∀-intro f) a x = (f x) ⟨$⟩ a
  cong  (∀-intro f) eq x = cong (f x) eq

  ∀-elim : ∀ {X : Set ℓ}{A : Pred X {ℓ}{ℓ}{ℓ}} x → Ofes [ ∀[ X ] A , A x ]
  _⟨$⟩_ (∀-elim x) f = f x
  cong  (∀-elim x) feq = feq x

  ►∀ : ∀ {X : Set ℓ}{A : Pred X {ℓ}{ℓ}{ℓ}} → ► (∀[ X ] A) ⇒ (∀[ X ] (λ a → ► (A a)))
  _⟨$⟩_ ►∀ (next f) a = next (f a)
  cong ►∀ LaterOfe.now a = LaterOfe.now
  cong ►∀ (next feq) a = LaterOfe.next (feq a)
