open import Relation.Binary hiding (_⇒_)

module Experiments.Partiality {ℓ₁ ℓ₂ ℓ₃} (APO : Preorder ℓ₁ ℓ₂ ℓ₃) where

import Function as Fun
open import Level

open import Experiments.Category APO hiding (_≅_;_≗_)

module Delayed where

  open import Size
  import Level

  mutual
    data Delay {ℓ}(i : Size)(A : Set ℓ) : Set (Level.suc ℓ) where
      now   : A → Delay i A
      later : ∞Delay i A → Delay i A

    record ∞Delay {ℓ}(i : Size)(A : Set ℓ) : Set (Level.suc ℓ) where
      coinductive
      field
        force : {j : Size< i} → Delay i A

  open ∞Delay
  open import Function

  mutual
    fmap : ∀ {ℓ ℓ₂}{A : Set ℓ}{B : Set ℓ₂} → (A → B) → Delay ∞ A → Delay ∞ B
    fmap f (now x) = now (f x)
    fmap f (later x) = later (∞fmap f x)

    ∞fmap : ∀ {ℓ ℓ₂}{A : Set ℓ}{B : Set ℓ₂} → (A → B) → ∞Delay ∞ A → ∞Delay ∞ B
    force (∞fmap f z) = fmap f (force z)

  -- strong bisimilarity
  mutual

    data _≅_ {i : Size}{ℓ}{A : Set ℓ} : (?a ?b : Delay ∞ A) → Set where
      now   : ∀ (a : A) → now a ≅ now a
      later : ∀ {∞a ∞b}(eq : ∞a ∞≅⟨ i ⟩ ∞b) → later ∞a ≅ later ∞b

    _≅⟨_⟩_ : ∀ {ℓ}{A : Set ℓ} → Delay ∞ A → Size → Delay ∞ A → Set
    _≅⟨_⟩_ = λ a? i b? → _≅_ {i = i} a? b?

    record _∞≅⟨_⟩_ {ℓ}{A : Set ℓ} (∞a : ∞Delay ∞ A) i (∞b : ∞Delay ∞ A) : Set where
      coinductive
      field
        ≅force : {j : Size< i} → (force ∞a) ≅⟨ j ⟩ force ∞b

  open _∞≅⟨_⟩_ public

  _∞≅_ : ∀ {i : Size}{ℓ}{A : Set ℓ} (∞a : ∞Delay ∞ A) (∞b : ∞Delay ∞ A) → Set
  _∞≅_ {i} a∞ b∞ = a∞ ∞≅⟨ i ⟩ b∞

  open import Relation.Binary.PropositionalEquality

  mutual
    fmap-id : ∀ {ℓ}{A : Set ℓ}{f : A → A}(fid : ∀ a → f a ≡ a) p → fmap f p ≅ p
    fmap-id fid (now x) rewrite fid x = now x
    fmap-id fid (later x) = later (∞fmap-id fid x)

    ∞fmap-id : ∀ {ℓ}{A : Set ℓ}{f : A → A}(fid : ∀ a → f a ≡ a)(p : ∞Delay ∞ A) →
               ∞fmap f p ∞≅ p
    ≅force (∞fmap-id fid p) = fmap-id fid (force p)

  mutual
    fmap-cong : ∀ {ℓ ℓ₁}{A : Set ℓ}{B : Set ℓ₁}{f g : A → B} → f ≗ g → ∀ x → fmap f x ≅ fmap g x
    fmap-cong peq (now x) rewrite peq x = now _
    fmap-cong peq (later x) = later (∞fmap-cong peq x)

    ∞fmap-cong : ∀ {ℓ ℓ₁}{A : Set ℓ}{B : Set ℓ₁}{f g : A → B} → f ≗ g → ∀ x → ∞fmap f x ∞≅ ∞fmap g x
    ≅force (∞fmap-cong peq x) = fmap-cong peq (force x)

  mutual
    fmap-compose : ∀ {ℓ ℓ₁ ℓ₂}{A : Set ℓ}{B : Set ℓ₁}{C : Set ℓ₂}
                   (f : A → B)(g : B → C)(a : Delay ∞ A) → fmap (g Fun.∘ f) a ≅ fmap g (fmap f a)
    fmap-compose f g (now x) = now (g (f x))
    fmap-compose f g (later x) = later (∞fmap-compose f g x)

    ∞fmap-compose : ∀ {ℓ ℓ₁ ℓ₂}{A : Set ℓ}{B : Set ℓ₁}{C : Set ℓ₂}
             (f : A → B)(g : B → C)(a : ∞Delay ∞ A) → ∞fmap (g Fun.∘ f) a ∞≅ ∞fmap g (∞fmap f a)
    ≅force (∞fmap-compose f g a) = fmap-compose f g (force a)

  postulate ≅-to-≡ : ∀ {ℓ}{A : Set ℓ}{a b : Delay ∞ A} → a ≅ b → a ≡ b

  _⊥ : ∀ {ℓ} → MP ℓ → MP (suc ℓ)
  (P ⊥) = mp
    (λ c → Delay ∞ (P · c))
    (record {
      monotone = λ w p → fmap (MP.monotone P w) p
      ; monotone-refl = λ {c} p → ≅-to-≡ (fmap-id (MP.monotone-refl P) p)
      ; monotone-trans = λ p c≤c' c'≤c'' →
        trans
          (≅-to-≡ (fmap-cong (λ p → MP.monotone-trans P p c≤c' c'≤c'') p ))
          (≅-to-≡ (fmap-compose (MP.monotone P c≤c') (MP.monotone P c'≤c'') p))
    })
