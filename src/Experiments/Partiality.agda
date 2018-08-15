open import Relation.Binary hiding (_⇒_)

module Experiments.Partiality {ℓ₁ ℓ₂ ℓ₃} (APO : Preorder ℓ₁ ℓ₂ ℓ₃) where

import Function as Fun
open import Level
open import Size

open import Experiments.Category APO hiding (_≅_;_≗_)

mutual
  data Delay {ℓ}(i : Size)(A : Set ℓ) : Set (Level.suc ℓ) where
    now   : A → Delay i A
    later : ∞Delay i A → Delay i A

  record ∞Delay {ℓ}(i : Size)(A : Set ℓ) : Set (Level.suc ℓ) where
    coinductive
    field
      force : {j : Size< i} → Delay j A

open ∞Delay
open import Function

module StrongBisimilarity where
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

  mutual
    refl : ∀ {ℓ}{A : Set ℓ} {a∞ : Delay ∞ A} → a∞ ≅ a∞
    refl {a∞ = now x} = now x
    refl {a∞ = later x} = later ∞refl

    ∞refl : ∀ {i ℓ}{A : Set ℓ} {a∞ : ∞Delay ∞ A} → a∞ ∞≅⟨ i ⟩ a∞
    ≅force (∞refl {a∞ = a∞}) = refl

  mutual
    sym : ∀ {i}{ℓ}{A : Set ℓ} {a∞ b∞ : Delay ∞ A} → a∞ ≅⟨ i ⟩ b∞ → b∞ ≅⟨ i ⟩ a∞
    sym (now a) = now a
    sym (later eq) = later (∞sym eq)

    ∞sym : ∀ {i ℓ}{A : Set ℓ} {a∞ b∞ : ∞Delay ∞ A} → a∞ ∞≅⟨ i ⟩ b∞ → b∞ ∞≅⟨ i ⟩ a∞
    ≅force (∞sym z) = sym (≅force z)

  mutual
    trans : ∀ {i}{ℓ}{A : Set ℓ} {a∞ b∞ c∞ : Delay ∞ A} → a∞ ≅⟨ i ⟩ b∞ → b∞ ≅⟨ i ⟩ c∞ → a∞ ≅⟨ i ⟩ c∞
    trans (now a) (now .a) = now a
    trans (later eq) (later eq₁) = later (∞trans eq eq₁)

    ∞trans : ∀ {i}{ℓ}{A : Set ℓ} {a∞ b∞ c∞ : ∞Delay ∞ A} → a∞ ∞≅⟨ i ⟩ b∞ → b∞ ∞≅⟨ i ⟩ c∞ → a∞ ∞≅⟨ i ⟩ c∞
    ≅force (∞trans p q) = trans (≅force p) (≅force q)

  open import Relation.Binary.PropositionalEquality as PEq
  postulate ≅-to-≡ : ∀ {ℓ}{A : Set ℓ}{a b : Delay ∞ A} → a ≅ b → a PEq.≡ b

module Functor where
  open StrongBisimilarity
  open import Relation.Binary.PropositionalEquality as PEq

  mutual
    fmap : ∀ {ℓ ℓ₂}{A : Set ℓ}{B : Set ℓ₂} → (A → B) → Delay ∞ A → Delay ∞ B
    fmap f (now x) = now (f x)
    fmap f (later x) = later (∞fmap f x)

    ∞fmap : ∀ {ℓ ℓ₂}{A : Set ℓ}{B : Set ℓ₂} → (A → B) → ∞Delay ∞ A → ∞Delay ∞ B
    force (∞fmap f z) = fmap f (force z)

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

module Monad where
  open StrongBisimilarity

  mutual
    bind : ∀ {ℓ ℓ₂}{A : Set ℓ}{B : Set ℓ₂} → (A → Delay ∞ B) → Delay ∞ A → Delay ∞ B
    bind f (now x) = f x
    bind f (later x) = later (∞bind f x)

    ∞bind : ∀ {ℓ ℓ₂}{A : Set ℓ}{B : Set ℓ₂} → (A → Delay ∞ B) → ∞Delay ∞ A → ∞Delay ∞ B
    force (∞bind f z) = bind f (force z)

  join : ∀ {ℓ}{A : Set ℓ} → Delay ∞ (Delay ∞ A) → Delay ∞ A
  join p = bind Fun.id p

  open Functor
  mutual
    join-natural : ∀ {i p q}{P : Set p}{Q : Set q}(f : P → Q) x →
                   (join Fun.∘ (fmap (fmap f))) x ≅⟨ i ⟩ ((fmap f) Fun.∘ join) x
    join-natural f (now x) = refl
    join-natural f (later x) = later (∞join-natural f x)

    ∞join-natural : ∀ {i p q}{P : Set p}{Q : Set q}(f : P → Q) x →
                    (∞bind Function.id Fun.∘ ∞fmap (fmap f)) x ∞≅⟨ i ⟩ (∞fmap f Fun.∘ ∞bind Fun.id) x
    ≅force (∞join-natural f p) = join-natural f (force p)

  return : ∀ {ℓ}{A : Set ℓ} → A → Delay ∞ A
  return = now

module Monotone where
  open Functor
  open StrongBisimilarity
  open import Relation.Binary.PropositionalEquality as PEq

  -- delayed monotone predicates are monotone predicates
  infixl 100 _⊥
  _⊥ : ∀ {ℓ} → MP ℓ → MP (suc ℓ)
  (P ⊥) = mp
    (λ c → Delay ∞ (P · c))
    (record {
      monotone = λ w p → fmap (MP.monotone P w) p
      ; monotone-refl = λ {c} p → ≅-to-≡ (fmap-id (MP.monotone-refl P) p)
      ; monotone-trans = λ p c≤c' c'≤c'' →
        PEq.trans
          (≅-to-≡ (fmap-cong (λ p → MP.monotone-trans P p c≤c' c'≤c'') p ))
          (≅-to-≡ (fmap-compose (MP.monotone P c≤c') (MP.monotone P c'≤c'') p))
    })

  -- unfortunately it doesn't follow immediately that it is also a monad in the category of
  -- MPs; we have to prove that the bind and return are morphisms.
  open Monad

  η : ∀ {p}(P : MP p) → P ⇒ P ⊥
  η P = mk⇒ return λ c~c' → PEq.refl

  μ : ∀ {p}(P : MP p) → (P ⊥) ⊥ ⇒ P ⊥
  μ P = mk⇒ join λ c~c' {p} → ≅-to-≡ (join-natural (MP.monotone P c~c') p)
