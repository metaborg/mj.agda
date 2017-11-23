open import Level

module Categorical.Ofe.Products where

open import Data.Product
open import Relation.Binary using (IsEquivalence)
import Relation.Binary.PropositionalEquality as PEq
import Data.Unit as Unit
import Function as Fun

open import Categories.Category
open import Categories.Support.Equivalence
open import Categories.Object.Terminal
open import Categories.Object.BinaryProducts
open import Categories.Object.Products
open import Categories.Monoidal
open import Categories.Monoidal.Cartesian

open import Categorical.Ofe
open import Categorical.Ofe.Cofe

open Category
open Ofe

module _ {o e e' : Level} where
  -- universe polymorphism without cumulatively made this a little harder than just using Δ

  ≈⊤ : ∀ {a ℓ}{A : Set a} → A → A → Set ℓ
  ≈⊤ _ _ = Lift Unit.⊤

  equiv-≈⊤ : ∀ {a ℓ}{A : Set a} → IsEquivalence (≈⊤ {ℓ = ℓ}{A = A})
  equiv-≈⊤ = record
    { refl = lift Unit.tt ; sym = λ x → lift Unit.tt ; trans = λ x x₁ → lift Unit.tt }

  oid : Setoid o e
  oid = record
    { Carrier = Lift Unit.⊤
    ; _≈_ = ≈⊤
    ; isEquivalence = equiv-≈⊤ }

  ⊤ : Terminal (Ofes {o}{e}{e'})
  ⊤ = record
    { ⊤ = record
        { setoid = oid
        ; _≈⟨_⟩_ = λ x _ y → ≈⊤ x y
        ; equiv = equiv-≈⊤
        ; limit₁ = λ _ _ → lift Unit.tt
        ; limit₂ = λ _ → lift Unit.tt
        ; monotone = λ _ _ → lift Unit.tt
        }
    ; ! = record { _⟨$⟩_ = λ _ → lift Unit.tt ; cong = λ _ → lift Unit.tt }
    ; !-unique = λ _ _ → lift Unit.tt }

module _ {s₁ s₂ e}(A B : Ofe s₁ s₂ e) where
  _×-ofe_ : Obj (Ofes {s₁}{s₂}{e})
  setoid _×-ofe_ = setoid A ×-setoid setoid B
  _≈⟨_⟩_ _×-ofe_ (l , r) n (l' , r') = A [ l ≈⟨ n ⟩ l' ] × B [ r ≈⟨ n ⟩ r' ]
  equiv _×-ofe_ = record
    { refl = ≈ₙ-refl A , Ofe.≈ₙ-refl B
    ; sym = λ eq → ≈ₙ-sym A (proj₁ eq) , ≈ₙ-sym B (proj₂ eq)
    ; trans = λ eq eq' →
      ≈ₙ-trans A (proj₁ eq) (proj₁ eq') ,
      ≈ₙ-trans B (proj₂ eq) (proj₂ eq') }
  limit₁ _×-ofe_ = λ x n → limit₁ A (proj₁ x) n , limit₁ B (proj₂ x) n
  limit₂ _×-ofe_ = λ eq → limit₂ A (proj₁ Fun.∘ eq) , limit₂ B (proj₂ Fun.∘ eq)
  monotone _×-ofe_ = λ n≥n' eq → monotone A n≥n' (proj₁ eq) , monotone B n≥n' (proj₂ eq)

  π₁ : Ofes [ _×-ofe_ , A ]
  _⟨$⟩_ π₁ (l , _) = l
  cong π₁ (leq , _) = leq

  π₂ : Ofes [ _×-ofe_ , B ]
  _⟨$⟩_ π₂ (_ , r) = r
  cong π₂ (_ , req) = req

  ⟨_,_⟩ : ∀ {C} → Ofes [ C , A ] → Ofes [ C , B ] → Ofes [ C , _×-ofe_ ]
  _⟨$⟩_ ⟨ F , G ⟩ c = F ⟨$⟩ c , G ⟨$⟩ c
  cong  ⟨ F , G ⟩ eq = cong F eq , cong G eq

  .comm₁ : ∀ {C}{f : Ofes [ C , A ]}{g : Ofes [ C , B ]} → Ofes [ Ofes [ π₁ ∘ ⟨ f , g ⟩ ] ≡ f ]
  comm₁ {f = f} x≈y = NE.≈-cong _ _ f x≈y

  .comm₂ : ∀ {C}{f : Ofes [ C , A ]}{g : Ofes [ C , B ]} → Ofes [ Ofes [ π₂ ∘ ⟨ f , g ⟩ ] ≡ g ]
  comm₂ {g = g} x≈y = NE.≈-cong _ _ g x≈y

  .univ : ∀ {C} {f : Ofes [ C , A ]}{g : Ofes [ C , B ]}{i : Ofes [ C , _×-ofe_ ]} →
         Ofes [ Ofes [ π₁ ∘ i ] ≡ f ] → Ofes [ Ofes [ π₂ ∘ i ] ≡ g ] → Ofes [ ⟨ f , g ⟩ ≡ i ]
  univ {C} p q eq = let eq' = ≈-sym C eq in ≈-sym A (p eq') , ≈-sym B (q eq')

open BinaryProducts using (product)

binary-products : ∀ {s₁ s₂ e} → BinaryProducts (Ofes {s₁}{s₂}{e})
product binary-products {A} {B} = record {
  A×B = A ×-ofe B
  ; π₁ = π₁ A B
  ; π₂ = π₂ A B
  ; ⟨_,_⟩ = ⟨_,_⟩ A B
  ; commute₁ = λ{ {f = f}{g} → comm₁ A B {f = f}{g} }
  ; commute₂ = λ{ {f = f}{g} → comm₂ A B {f = f}{g} }
  ; universal = λ{ {f = f}{g}{i} → univ A B {f = f}{g}{i} }}

products : ∀ {s₁ s₂ e} → Products (Ofes {s₁}{s₂}{e})
products = record {
  terminal = ⊤ ;
  binary = binary-products }

monoidal : ∀ {s₁ s₂ e} → Monoidal (Ofes {s₁}{s₂}{e})
monoidal = Cartesian Ofes products

open Cofe

-- taking products of cofes preserves completeness
_×-cofe_ : ∀ {o e e'}(A B : Cofe o e e') → Cofe o e e'
A ×-cofe B = record
  { ofe = (ofe A) ×-ofe (ofe B)
  ; conv = λ c →
    let
      l = conv A (chain-map (π₁ (ofe A) (ofe B)) c)
      r = Cofe.conv B (chain-map (π₂ (ofe A) (ofe B)) c)
    in lim (at-∞ l , at-∞ r) (λ n → limit l n , limit r n) }
