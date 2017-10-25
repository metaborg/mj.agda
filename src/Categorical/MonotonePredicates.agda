open import Categorical.Preorder

module Categorical.MonotonePredicates {ℓ₁ ℓ₂ ℓ₃} (po : PreorderPlus ℓ₁ ℓ₂ ℓ₃) where

import Function as Fun
import Relation.Binary.PropositionalEquality as PEq

open import Level
open import Data.Product

open import Categories.Agda
open import Categories.Category
open import Categories.Presheaf
open import Categories.Presheaves
open import Categories.Functor
open import Categories.Bifunctor
open import Categories.Monoidal
open import Categories.Support.Equivalence
open import Categories.Support.SetoidFunctions as SF
open import Categories.Support.EqReasoning
open import Categories.Object.BinaryProducts
open import Categories.Object.Products
open import Categories.Monoidal.Cartesian
open import Categories.NaturalTransformation
open import Relation.Binary.Product.Pointwise hiding (_×-setoid_)

open Category
open Functor
open _⟶_
open NaturalTransformation
open Setoid

MP : Category _ _ _
MP = Presheaves (Preorder po)

open import Categories.Object.Terminal MP
import Data.Unit as Unit

≡-setoid : ∀ {ℓ} → Set ℓ → Setoid _ _
≡-setoid A = record { Carrier = A ; _≈_ = PEq._≡_ ; isEquivalence = PEq.isEquivalence }

terminal : Terminal
terminal = record {
  ⊤ = record {
      F₀ = λ _ → ≡-setoid (Lift Unit.⊤)
    ; F₁ = λ c≤c' → record { _⟨$⟩_ = λ x → lift Unit.tt ; cong = λ x → PEq.refl }
    ; identity = λ _ → PEq.refl
    ; homomorphism = λ _ → PEq.refl
    ; F-resp-≡ = λ _ _ → PEq.refl
  }
  ; ! = record {
      η = λ X → record { _⟨$⟩_ = λ x → lift Unit.tt ; cong = λ x → PEq.refl }
    ; commute = λ _ _ → PEq.refl }
  ; !-unique = λ _ _ → PEq.refl }

-- TODO is this construction general for all presheaves-categories?
-- i.e. is it domain independent
open BinaryProducts using (product)
products : BinaryProducts MP
product products {A} {B} = record {
  A×B = A×B
  ; π₁ = π₁
  ; π₂ = π₂
  ; ⟨_,_⟩ = ⟨_,_⟩
  ; commute₁ = {!!}
  ; commute₂ = {!!}
  ; universal = {!!} }

  where
    private
      module A = Functor A
      module B = Functor B
      module Po = Category (Preorder po)
      module Is = Category (ISetoids ℓ₃ ℓ₃)

    -- pointwise product
    omap = λ c → (A.F₀ c) ×-setoid (B.F₀ c)

    -- pointwise lifting of a morphisms
    hmap : ∀ {c c'} → Po.op [ c , c' ] → ISetoids _ _ [ omap c , omap c' ]
    hmap c≤c' = record {
        _⟨$⟩_ = λ{ (l , r) → A.F₁ c≤c' ⟨$⟩ l , B.F₁ c≤c' ⟨$⟩ r  }
      ; cong  = λ{ (l , r) → cong (A.F₁ c≤c') l , cong (B.F₁ c≤c') r }}

    .identity′ : ∀ {c} → ISetoids _ _ [ hmap {c} Po.id ≡ Is.id ]
    identity′ {c} {x = x}{y , y'}(p , q) = left , right
      where
        left = begin
            A.F₁ Po.id ⟨$⟩ (proj₁ x)
              ≈⟨ identity A (refl (A.F₀ c)) ⟩
            proj₁ x
              ≈⟨ p ⟩
            y ∎
          where open SetoidReasoning (A.F₀ c)
        right = begin
            B.F₁ Po.id ⟨$⟩ (proj₂ x)
              ≈⟨ identity B (refl (B.F₀ c)) ⟩
            proj₂ x
              ≈⟨ q ⟩
            y' ∎
          where open SetoidReasoning (B.F₀ c)

    .F-resp-≡′ : ∀ {a b : Po.Obj}{F G : Po.op [ a , b ]} → Po.op [ F ≡ G ] → ISetoids _ _ [ hmap F ≡ hmap G ]
    F-resp-≡′ {b = b}{F}{G} F≡G {x = x}{y} x≡y =
      begin
        hmap F ⟨$⟩ x
          ≈⟨ cong (hmap F) x≡y ⟩
        hmap F ⟨$⟩ y
          ↓≣⟨ PEq.cong (λ u → hmap u ⟨$⟩ y) F≡G ⟩
        hmap G ⟨$⟩ y ∎
      where open SetoidReasoning (omap b)

    .homomorphism′ : ∀ {a b c : Po.Obj}{f : Po.op [ a , b ]}{g : Po.op [ b , c ]} →
                    ISetoids _ _ [ hmap (Po.op [ g ∘ f ]) ≡ ISetoids _ _ [ hmap g ∘ hmap f ] ]
    homomorphism′ {a}{c = c}{f}{g}{x}{y} x≡y =
      begin
        hmap (Po.op [ g ∘ f ]) ⟨$⟩ x
          ≈⟨ cong (hmap (Po.op [ g ∘ f ])) x≡y ⟩
        hmap (Po.op [ g ∘ f ]) ⟨$⟩ y
          ↓≣⟨ PEq.refl ⟩
        let h = (Po.op [ g ∘ f ]) in ((A.F₁ h) ⟨$⟩ (proj₁ y) , (B.F₁ h) ⟨$⟩ (proj₂ y))
          ≈⟨ homomorphism A (refl (A.F₀ a)) , homomorphism B (refl (B.F₀ a)) ⟩
        (A.F₁ g) ⟨$⟩ ((A.F₁ f) ⟨$⟩ (proj₁ y)) , (B.F₁ g) ⟨$⟩ ((B.F₁ f) ⟨$⟩ (proj₂ y))
          ↓≣⟨ PEq.refl ⟩
        (hmap g) ∙ (hmap f) ⟨$⟩ y
          ↓≣⟨ PEq.refl ⟩
        ISetoids _ _ [ hmap g ∘ hmap f ] ⟨$⟩ y ∎
      where open SetoidReasoning (omap c)

    A×B : Obj MP
    A×B = record {
        F₀ = omap
      ; F₁ = hmap
      ; identity = identity′
      ; homomorphism = homomorphism′
      ; F-resp-≡ = F-resp-≡′ }

    π₁ : MP [ A×B , A ]
    π₁ = record {
        η = λ c → record { _⟨$⟩_ = proj₁ ; cong = proj₁ }
      ; commute = {!!} }

    π₂ : MP [ A×B , B ]
    π₂ = record {
        η = λ c → record { _⟨$⟩_ = proj₂ ; cong = proj₂ }
      ; commute = {!!} }

    ⟨_,_⟩ : ∀ {C} → MP [ C , A ] → MP [ C , B ] → MP [ C , A×B ]
    ⟨_,_⟩ C⇒A C⇒B = record {η = λ X → ⟪ η C⇒A X , η C⇒B X ⟫ ; commute = λ f x₁ → {!!} , {!!} }

has-products : Products MP
has-products = record {
  terminal = terminal ;
  binary = products }

cartesian : Monoidal MP
cartesian = Cartesian MP record {
  terminal = terminal ;
  binary = products }
