open import Categorical.Preorder

module Categorical.MonotonePredicates {ℓ₁ ℓ₂} (po : PreorderPlus ℓ₁ ℓ₂ ℓ₁) where

import Function as Fun
import Relation.Binary.PropositionalEquality as PEq

open import Level
open import Data.Product

open import Categories.Agda
open import Categories.Category
open import Categories.Presheaf
open import Categories.Presheaves
open import Categories.Functor using (Functor)
open import Categories.Monoidal
open import Categories.Support.Equivalence
open import Categories.Support.SetoidFunctions as SF
open import Categories.Support.EqReasoning
open import Categories.Object.BinaryProducts
open import Categories.Object.Products
open import Categories.Monoidal.Cartesian
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Relation.Binary.Product.Pointwise hiding (_×-setoid_)

open Category
open Functor
open _⟶_
open NaturalTransformation using (η; commute)
open Setoid

private
  C = Category.op (Preorder po)

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
  ; commute₁ = λ{ {f = f}{g} → commute₁ {f = f}{g} }
  ; commute₂ = λ{ {f = f}{g} → commute₂ {f = f}{g} }
  ; universal = λ{ {f = f}{g}{i} → universal {f = f}{g}{i} }}

  where
    private
      module A = Functor A
      module B = Functor B
      module Po = Category (Preorder po)
      module Is = Category (ISetoids ℓ₁ ℓ₁)

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
    η π₁ c = record { _⟨$⟩_ = proj₁ ; cong = proj₁ }
    commute π₁ f (x≡x' , _) = cong (A.F₁ f) x≡x'

    π₂ : MP [ A×B , B ]
    η π₂ c = record { _⟨$⟩_ = proj₂ ; cong = proj₂ }
    commute π₂ f (_ , y≡y') = cong (B.F₁ f) y≡y'

    ⟨_,_⟩ : ∀ {C} → MP [ C , A ] → MP [ C , B ] → MP [ C , A×B ]
    η ⟨ C⇒A , C⇒B ⟩ X = ⟪ η C⇒A X , η C⇒B X ⟫
    commute (⟨_,_⟩ {C} C⇒A C⇒B) f x≡y = commute C⇒A f x≡y , commute C⇒B f x≡y

    .commute₁ : ∀ {C} {f : (MP ⇒ C) A} {g : (MP ⇒ C) B} → (MP ≡ (MP ∘ π₁) ⟨ f , g ⟩) f
    commute₁ {f = f}{x = x} p = cong (η f x) p

    .commute₂ : ∀ {C} {f : (MP ⇒ C) A} {g : (MP ⇒ C) B} → (MP ≡ (MP ∘ π₂) ⟨ f , g ⟩) g
    commute₂ {g = g}{x = x} p = cong (η g x) p

    .universal : ∀ {C} {f : MP [ C , A ]} {g : MP [ C , B ]} {i : MP [ C , A×B ]} →
                 MP [ MP [ π₁ ∘ i ] ≡ f ] → MP [ MP [ π₂ ∘ i ] ≡ g ] → MP [ ⟨ f , g ⟩ ≡ i ]
    universal {C} l r {x} p = sym (A.F₀ x) (l (sym (F₀ C x) p)) , sym (B.F₀ x) (r (sym (F₀ C x) p))

has-products : Products MP
has-products = record {
  terminal = terminal ;
  binary = products }

cartesian : Monoidal MP
cartesian = Cartesian MP record {
  terminal = terminal ;
  binary = products }

-- TODO this seems a construction that should work for any presheaf category
-- forall quantification lower-bounded by an object from our preorder
module Forall≥ (P : PreorderPlus.Carrier po → Setoid ℓ₁ ℓ₁) where

  open PreorderPlus po hiding (po; Carrier)

  -- morally we have: omap x ≔ ∀ x' → x ⇒ x' → P x'
  omap = λ x → ∀[ PreorderPlus.Carrier po ]-setoid λ x' → ∀[ C [ x , x' ] ]-setoid λ _ → P x'

  hmap : ∀ {A B} → C [ A , B ] → ISetoids ℓ₁ ℓ₁ [ omap A , omap B ]
  _⟨$⟩_ (hmap A⇒B) f X B⇒X = f X (C [ B⇒X ∘ A⇒B ])
  cong (hmap A⇒B) f≡g X B⇒Y = f≡g X (C [ B⇒Y ∘ A⇒B ])

  obj : Obj MP
  F₀ obj X = omap X
  F₁ obj A⇒B = hmap A⇒B
  identity obj {x = f}{g} f≡g X A⇒X =
    begin
       f X (C [ A⇒X ∘ Category.id C ])
         ↓≣⟨ PEq.cong (f X) (Category.identityʳ C) ⟩
       f X A⇒X
         ↓⟨ f≡g X A⇒X ⟩
       g X A⇒X ∎
    where open SetoidReasoning (P X)
  homomorphism obj {f = X⇒Y} {Y⇒Z} {x = f} {g} f≡g X Z⇒X = begin
      f X (C [ Z⇒X ∘ C [ Y⇒Z ∘ X⇒Y ] ])
        ↓⟨ f≡g X _ ⟩
      g X (C [ Z⇒X ∘ C [ Y⇒Z ∘ X⇒Y ] ])
        ↑≣⟨ PEq.cong (g X) (Category.assoc C) ⟩
      g X (C [ C [ Z⇒X ∘ Y⇒Z ] ∘ X⇒Y ])
        ↓≣⟨ PEq.refl ⟩
      (ISetoids ℓ₁ ℓ₁ [ hmap Y⇒Z ∘ hmap X⇒Y ] ⟨$⟩ g) X Z⇒X ∎
    where open SetoidReasoning (P X)
  F-resp-≡ obj {F = F}{G} F≡G {x = f}{g} f≡g X B⇒A = begin
    f X (C [ B⇒A ∘ F ])
      ↓≣⟨ PEq.cong (f X) (∘-resp-≡ C PEq.refl F≡G) ⟩
    f X (C [ B⇒A ∘ G ])
      ↓⟨ f≡g X _ ⟩
    g X (C [ B⇒A ∘ G ]) ∎
    where open SetoidReasoning (P X)

open Forall≥ using () renaming (obj to ∀[_]) public
