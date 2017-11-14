open import Categorical.Preorder

module Categorical.MonotonePredicates {ℓ₂ ℓ₃} (po : PreorderPlus ℓ₃ ℓ₂ ℓ₃) where

import Function as Fun
import Relation.Binary.PropositionalEquality as PEq

open import Level
open import Data.Product

open import Categories.Agda
open import Categories.Category
open import Categories.Presheaf
open import Categories.Presheaves
open import Categories.Functor using (Functor; _∘_) renaming (id to idF; const to constF)
open import Categories.Monoidal
open import Categories.Support.Equivalence
open import Categories.Support.SetoidFunctions as SF hiding (const)
open import Categories.Support.EqReasoning
open import Categories.Object.BinaryProducts
open import Categories.Object.Products
open import Categories.Monoidal.Cartesian
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Relation.Binary.Product.Pointwise hiding (_×-setoid_)

open Category
open _⟶_
open NaturalTransformation using (η; commute)
open Setoid
open Functor

private
  C = Category.op (Preorder po)

MP : Category _ _ _
MP = Presheaves (Preorder po)

open import Categories.Product
open import Categories.Bifunctor

≡-setoid : ∀ {ℓ} → Set ℓ → Setoid _ _
≡-setoid A = record { Carrier = A ; _≈_ = PEq._≡_ ; isEquivalence = PEq.isEquivalence }

open import Categories.Functor.Hom
open Hom

{-}
module HomProperties {o ℓ e}(C : Category o ℓ e) where
  open Setoids
  open import Categories.Morphisms (ISetoids ℓ e)
  open import Categories.Object.Product renaming (Product to _[_×_])
  open _[_×_] hiding (η)

  private
    Hom = F₀ Hom[ C ][-,-]

  open _≅_
  hom-preserves-× : ∀ {x y z : Obj C}{y×z : C [ y × z ]} →
                    Hom (x , (A×B y×z)) ≅ F₀ (A×BSetoid _ _) (Hom (x , y) , Hom (x , z))
  f (hom-preserves-× {y×z = y×z}) = record
    { _⟨$⟩_ = λ x⇒y×z → C [ π₁ y×z ∘ x⇒y×z ] , C [ π₂ y×z ∘ x⇒y×z ]
    ; cong = λ x → {!!}
    }
  g hom-preserves-× = {!!}
  iso hom-preserves-× = {!!}

open import Categories.Yoneda
open import Categories.NaturalIsomorphism
open NaturalIsomorphism
-}

{-}
A×B-MP : Bifunctor MP MP MP -- Functor (Product MP MP) MP
F₀ A×B-MP (P , Q) = FT._∘_ {!(η (F⇒G (yoneda ?)) ? ⟨$⟩ ?)!} {!!}
F₁ A×B-MP = {!!}
identity A×B-MP = {!!}
homomorphism A×B-MP = {!!}
F-resp-≡ A×B-MP = {!!}
-}

open import Categories.Object.Terminal
import Data.Unit as Unit

open import Categories.Yoneda
open import Categories.NaturalIsomorphism
open NaturalIsomorphism

terminal : Terminal MP
terminal = record {
  ⊤ = constF (set→setoid (Lift Unit.⊤))
  ; ! = record {
      η = λ X → record { _⟨$⟩_ = λ _ → lift Unit.tt ; cong = λ x → PEq.refl }
    ; commute = λ _ _ → PEq.refl }
  ; !-unique = λ _ _ → PEq.refl }

open Terminal terminal public

-- TODO is this construction general for all presheaves-categories?
-- i.e. is it domain independent
open BinaryProducts using (product)
products : BinaryProducts MP
product products {P} {Q} = record {
  A×B = P×Q
  ; π₁ = π₁
  ; π₂ = π₂
  ; ⟨_,_⟩ = ⟨_,_⟩
  ; commute₁ = λ{ {f = f}{g} → commute₁ {f = f}{g} }
  ; commute₂ = λ{ {f = f}{g} → commute₂ {f = f}{g} }
  ; universal = λ{ {f = f}{g}{i} → universal {f = f}{g}{i} }}

  where
    private
      module P = Functor P
      module Q = Functor Q
      module Po = Category (Preorder po)
      module Is = Category (ISetoids _ _)

    -- pointwise product
    omap = λ c → (P.F₀ c) ×-setoid (Q.F₀ c)

    -- pointwise lifting of a morphisms
    hmap : ∀ {c c'} → Po.op [ c , c' ] → ISetoids _ _ [ omap c , omap c' ]
    hmap c≤c' = record {
        _⟨$⟩_ = λ{ (l , r) → P.F₁ c≤c' ⟨$⟩ l , Q.F₁ c≤c' ⟨$⟩ r  }
      ; cong  = λ{ (l , r) → cong (P.F₁ c≤c') l , cong (Q.F₁ c≤c') r }}

    .identity′ : ∀ {c} → ISetoids _ _ [ hmap {c} Po.id ≡ Is.id ]
    identity′ {c} {x = x}{y , y'}(p , q) = left , right
      where
        left = begin
            P.F₁ Po.id ⟨$⟩ (proj₁ x)
              ≈⟨ Functor.identity P (refl (P.F₀ c)) ⟩
            proj₁ x
              ≈⟨ p ⟩
            y ∎
          where open SetoidReasoning (P.F₀ c)
        right = begin
            Q.F₁ Po.id ⟨$⟩ (proj₂ x)
              ≈⟨ Functor.identity Q (refl (Q.F₀ c)) ⟩
            proj₂ x
              ≈⟨ q ⟩
            y' ∎
          where open SetoidReasoning (Q.F₀ c)

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
        let h = (Po.op [ g ∘ f ]) in ((P.F₁ h) ⟨$⟩ (proj₁ y) , (Q.F₁ h) ⟨$⟩ (proj₂ y))
          ≈⟨ Functor.homomorphism P (refl (P.F₀ a)) , Functor.homomorphism Q (refl (Q.F₀ a)) ⟩
        (P.F₁ g) ⟨$⟩ ((P.F₁ f) ⟨$⟩ (proj₁ y)) , (Q.F₁ g) ⟨$⟩ ((Q.F₁ f) ⟨$⟩ (proj₂ y))
          ↓≣⟨ PEq.refl ⟩
        (hmap g) ∙ (hmap f) ⟨$⟩ y
          ↓≣⟨ PEq.refl ⟩
        ISetoids _ _ [ hmap g ∘ hmap f ] ⟨$⟩ y ∎
      where open SetoidReasoning (omap c)

    P×Q : Obj MP
    P×Q = record {
        F₀ = omap
      ; F₁ = hmap
      ; identity = identity′
      ; homomorphism = homomorphism′
      ; F-resp-≡ = F-resp-≡′ }

    π₁ : MP [ P×Q , P ]
    η π₁ c = record { _⟨$⟩_ = proj₁ ; cong = proj₁ }
    commute π₁ f (x≡x' , _) = cong (P.F₁ f) x≡x'

    π₂ : MP [ P×Q , Q ]
    η π₂ c = record { _⟨$⟩_ = proj₂ ; cong = proj₂ }
    commute π₂ f (_ , y≡y') = cong (Q.F₁ f) y≡y'

    ⟨_,_⟩ : ∀ {C} → MP [ C , P ] → MP [ C , Q ] → MP [ C , P×Q ]
    η ⟨ C⇒A , C⇒B ⟩ X = ⟪ η C⇒A X , η C⇒B X ⟫
    commute (⟨_,_⟩ {C} C⇒A C⇒B) f x≡y = commute C⇒A f x≡y , commute C⇒B f x≡y

    .commute₁ : ∀ {C} {f : (MP ⇒ C) P} {g : (MP ⇒ C) Q} → MP [ MP [ π₁ ∘ ⟨ f , g ⟩ ] ≡ f ]
    commute₁ {f = f}{x = x} p = cong (η f x) p

    .commute₂ : ∀ {C} {f : (MP ⇒ C) P} {g : (MP ⇒ C) Q} → MP [ MP [ π₂ ∘ ⟨ f , g ⟩ ] ≡ g ]
    commute₂ {g = g}{x = x} p = cong (η g x) p

    .universal : ∀ {C} {f : MP [ C , P ]} {g : MP [ C , Q ]} {i : MP [ C , P×Q ]} →
                 MP [ MP [ π₁ ∘ i ] ≡ f ] → MP [ MP [ π₂ ∘ i ] ≡ g ] → MP [ ⟨ f , g ⟩ ≡ i ]
    universal {C} l r {x} p = sym (P.F₀ x) (l (sym (Functor.F₀ C x) p)) , sym (Q.F₀ x) (r (sym (Functor.F₀ C x) p))

-- the category has finite products
has-products : Products MP
has-products = record {
  terminal = terminal ;
  binary = products }

-- the category is monoidal
monoidal : Monoidal MP
monoidal = Cartesian MP has-products

-- TODO this seems a construction that should work for any presheaf category
-- forall quantification lower-bounded by an object from our preorder
-- Robbert: this construction is also used in their logics
module Closure (P : PreorderPlus.Carrier po → Setoid ℓ₃ ℓ₃) where

  open PreorderPlus po hiding (po; Carrier)

  -- morally we have: omap x ≔ ∀ x' → x ⇒ x' → P x'
  omap = λ x → ∀[ PreorderPlus.Carrier po ]-setoid λ x' → ∀[ C [ x , x' ] ]-setoid λ _ → P x'

  hmap : ∀ {A B} → C [ A , B ] → ISetoids _ _ [ omap A , omap B ]
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
      (ISetoids _ _ [ hmap Y⇒Z ∘ hmap X⇒Y ] ⟨$⟩ g) X Z⇒X ∎
    where open SetoidReasoning (P X)
  F-resp-≡ obj {F = F}{G} F≡G {x = f}{g} f≡g X B⇒A = begin
    f X (C [ B⇒A ∘ F ])
      ↓≣⟨ PEq.cong (f X) (Category.∘-resp-≡ C PEq.refl F≡G) ⟩
    f X (C [ B⇒A ∘ G ])
      ↓⟨ f≡g X _ ⟩
    g X (C [ B⇒A ∘ G ]) ∎
    where open SetoidReasoning (P X)

open Closure using () renaming (obj to ∀-closure[_]) public
