module Categorical.ISetoids.Monads.Delay where

open import Categories.Category
open import Categories.Functor.Core renaming (id to idF; _∘_ to _∘F_)
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.Monad
open import Categories.Agda
open import Categories.Support.Equivalence
open import Categories.Support.SetoidFunctions as SF hiding (id)

open import Categorical.ISetoids.Equality

import Function as Fun
open import Level
open import Size

open Monad
open Functor
open Category

module DelayM {s₁ s₂} where

  ISets = ISetoids s₁ s₂

  open import Categorical.ISetoids.Delay

  omap : Obj ISets → Obj ISets
  omap A = delay-setoid A

  ∞omap : Obj ISets → Obj ISets
  ∞omap A = ∞delay-setoid A

  mutual
    hmap : {A B : Obj ISets} → ISets [ A , B ] → ISets [ omap A , omap B ]
    _⟨$⟩_ (hmap A⇒B) (now x) = now (A⇒B ⟨$⟩ x)
    _⟨$⟩_ (hmap A⇒B) (later ∞x) = later (∞hmap A⇒B ⟨$⟩ ∞x)
    cong (hmap A⇒B) (now eq) = now (cong A⇒B eq)
    cong (hmap A⇒B) (later eq) = later (cong (∞hmap A⇒B) eq)

    ∞hmap : ∀ {A B} → ISets [ A , B ] → ISets [ ∞omap A , ∞omap B ]
    force (_⟨$⟩_ (∞hmap f) x) = hmap f ⟨$⟩ force x
    ≅force (cong (∞hmap f) eq) = cong (hmap _) (≅force eq)

  mutual
    identity′ : ∀ {A : Obj ISets}{x y} →
                (omap A) [ x ≈ y ] → omap A [ hmap (id ISets) ⟨$⟩ x ≈ y ]
    identity′ (now eq) = now eq
    identity′ (later eq) = later (∞identity eq)

    ∞identity : ∀ {A : Obj ISets}{x y} →
                (∞omap A) [ x ≈ y ] → ∞omap A [ ∞hmap (id ISets) ⟨$⟩ x ≈ y ]
    ≅force (∞identity eq) = identity′ (≅force eq)

  mutual
    .homomorphism′ : ∀ {A B C : Obj ISets}{x y}{g : ISets [ B , C ]}{f : ISets [ A , B ]} →
                    (omap A) [ x ≈ y ] →
                    (omap C) [ hmap (ISets [ g ∘ f ]) ⟨$⟩ x ≈ ISets [ hmap g ∘ hmap f ] ⟨$⟩ y ]
    homomorphism′ {g = g}{f = f} (now eq) = now (cong (ISetoids _ _ [ g ∘ f ]) eq)
    homomorphism′ (later eq) = later (∞homomorphism eq)

    .∞homomorphism : ∀ {A B C : Obj ISets}{x y}{g : ISets [ B , C ]}{f : ISets [ A , B ]} →
                    (∞omap A) [ x ≈ y ] →
                    (∞omap C) [ ∞hmap (ISets [ g ∘ f ]) ⟨$⟩ x ≈ ISets [ ∞hmap g ∘ ∞hmap f ] ⟨$⟩ y ]
    ≅force (∞homomorphism eq) = homomorphism′ (≅force eq)

  mutual
     .F-resp : ∀ {A B}{F G : ISets [ A , B ]} →
               ISets [ F ≡ G ] → ISets [ hmap F ≡ hmap G ]
     F-resp F≡G (now x≡y) = now (F≡G x≡y)
     F-resp F≡G (later x≡y) = later (∞F-resp F≡G x≡y)

     .∞F-resp : ∀ {A B}{F G : ISets [ A , B ]} →
                ISets [ F ≡ G ] → ISets [ ∞hmap F ≡ ∞hmap G ]
     ≅force (∞F-resp F≡G eq) = F-resp F≡G (≅force eq)

  delayF : Endofunctor ISets
  F₀ delayF = omap
  F₁ delayF = hmap
  identity delayF = identity′
  homomorphism delayF = homomorphism′
  F-resp-≡ delayF = F-resp

  ∞delayF : Endofunctor ISets
  F₀ ∞delayF = ∞omap
  F₁ ∞delayF = ∞hmap
  identity ∞delayF = ∞identity
  homomorphism ∞delayF = ∞homomorphism
  F-resp-≡ ∞delayF = ∞F-resp

  open NaturalTransformation
  η′ : NaturalTransformation idF delayF
  _⟨$⟩_ (η η′ A) a = now a
  cong (η η′ A) a≡b = now a≡b
  commute η′ f a≡b = now (cong f a≡b)

  mutual
    μ′ : NaturalTransformation (delayF ∘F delayF) delayF
    _⟨$⟩_ (η μ′ A) (now a) = a
    _⟨$⟩_ (η μ′ A) (later a) = later (η ∞μ A ⟨$⟩ a)
    cong (η μ′ A) (now eq) = eq
    cong (η μ′ A) {later x} (later eq) = later (cong (η ∞μ A) eq)
    commute μ′ f (now (now x)) = now (cong f x)
    commute μ′ f (now (later eq)) = later (cong (∞hmap f) eq)
    commute μ′ f (later eq) = later (commute ∞μ f eq)

    ∞μ : NaturalTransformation (∞delayF ∘F delayF) ∞delayF
    force (_⟨$⟩_ (η ∞μ A) a) = η μ′ A ⟨$⟩ (force a)
    ≅force (cong (η ∞μ A) a≡b) = cong (η μ′ A) (≅force a≡b)
    ≅force (commute ∞μ f eq) = commute μ′ f (≅force eq)

  mutual
    .assoc′ : ∀ {A}{x y} → (F₀ (delayF ∘F delayF ∘F delayF) A [ x ≈ y ]) →
            (omap A [ η (μ′ ∘₁ delayF ∘ˡ μ′) A ⟨$⟩ x ≈ (η (μ′ ∘₁ μ′ ∘ʳ delayF) A ⟨$⟩ y) ])
    assoc′ (now (now (now x))) = now x
    assoc′ (now (now (later eq))) = later eq
    assoc′ (now (later eq)) = later (cong (η ∞μ _) eq)
    assoc′ (later eq) = later (∞assoc eq)

    .∞assoc : ∀ {A}{∞a ∞b} →
             _∞≅⟨_⟩_ (F₀ (delayF ∘F delayF) A) ∞a ∞ ∞b →
             _∞≅⟨_⟩_ A ((η ∞μ A) ⟨$⟩ (∞hmap (η μ′ A) ⟨$⟩ ∞a)) ∞ (η ∞μ A ⟨$⟩ (η ∞μ (omap A) ⟨$⟩ ∞b))
    ≅force (∞assoc eq) = assoc′ (≅force eq)

  mutual
    .identityˡ′ : ∀ {A x y} → F₀ delayF A [ x ≈ y ] → omap A [ η (μ′ ∘₁ delayF ∘ˡ η′) A ⟨$⟩ x ≈ y ]
    identityˡ′ (now x) = now x
    identityˡ′ (later eq) = later (∞idˡ eq)

    ∞idˡ : ∀ {A ∞a ∞b} → _∞≅⟨_⟩_ A ∞a ∞ ∞b → _∞≅⟨_⟩_ A (η ∞μ A ⟨$⟩ (∞hmap (η η′ A) ⟨$⟩ ∞a)) ∞ ∞b
    ≅force (∞idˡ eq) = identityˡ′ (≅force eq)

  delayM : Monad ISets
  F delayM = delayF
  η delayM = η′
  μ delayM = μ′
  assoc delayM = assoc′
  identityˡ delayM = identityˡ′
  identityʳ delayM = Fun.id
