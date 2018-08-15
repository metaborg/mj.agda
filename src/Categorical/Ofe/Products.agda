open import Level

module Categorical.Ofe.Products where

open import Data.Product
open import Data.Product using (_,_) public
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
open import Categorical.Ofe.Cofe hiding (_⇨_)

open Category using (Obj)
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

  terminal : Terminal (Ofes {o}{e}{e'})
  terminal = record
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

  open Terminal terminal public

infixr 2 _×-ofe_
_×-ofe_ : ∀ {o e ℓ}{o' e' ℓ'} → Ofe o e ℓ → Ofe o' e' ℓ' → Obj Ofes
setoid (A ×-ofe B) = setoid A ×-setoid setoid B
_≈⟨_⟩_ (A ×-ofe B) (l , r) n (l' , r') = A [ l ≈⟨ n ⟩ l' ] × B [ r ≈⟨ n ⟩ r' ]
equiv (A ×-ofe B) = record
  { refl = ≈ₙ-refl A , Ofe.≈ₙ-refl B
  ; sym = λ eq → ≈ₙ-sym A (proj₁ eq) , ≈ₙ-sym B (proj₂ eq)
  ; trans = λ eq eq' →
    ≈ₙ-trans A (proj₁ eq) (proj₁ eq') ,
    ≈ₙ-trans B (proj₂ eq) (proj₂ eq') }
limit₁ (A ×-ofe B) = λ x n → limit₁ A (proj₁ x) n , limit₁ B (proj₂ x) n
limit₂ (A ×-ofe B) = λ eq → limit₂ A (proj₁ Fun.∘ eq) , limit₂ B (proj₂ Fun.∘ eq)
monotone (A ×-ofe B) = λ n≥n' eq → monotone A n≥n' (proj₁ eq) , monotone B n≥n' (proj₂ eq)

module BinProd {s₁ s₂ e}(A B : Ofe s₁ s₂ e) where

  π₁ : Ofes [ A ×-ofe B , A ]
  _⟨$⟩_ π₁ (l , _) = l
  cong π₁ (leq , _) = leq

  π₂ : Ofes [ A ×-ofe B , B ]
  _⟨$⟩_ π₂ (_ , r) = r
  cong π₂ (_ , req) = req

  ⟨_,_⟩ : ∀ {C} → Ofes [ C , A ] → Ofes [ C , B ] → Ofes [ C , A ×-ofe B ]
  _⟨$⟩_ ⟨ F , G ⟩ c = F ⟨$⟩ c , G ⟨$⟩ c
  cong  ⟨ F , G ⟩ eq = cong F eq , cong G eq

  .comm₁ : ∀ {C}{f : Ofes [ C , A ]}{g : Ofes [ C , B ]} → Ofes [ Ofes [ π₁ ∘ ⟨ f , g ⟩ ] ≡ f ]
  comm₁ {f = f} x≈y = cong f x≈y

  .comm₂ : ∀ {C}{f : Ofes [ C , A ]}{g : Ofes [ C , B ]} → Ofes [ Ofes [ π₂ ∘ ⟨ f , g ⟩ ] ≡ g ]
  comm₂ {g = g} x≈y = cong g x≈y

  -- a stronger universality proof, at a single level
  .≈ₙ-univ : ∀ {C} {f : Ofes [ C , A ]}{g : Ofes [ C , B ]}{i : Ofes [ C , A ×-ofe B ]}{n} →
             Ofes [ π₁ ∘ i ] ≡⟨ n ⟩ f → Ofes [ π₂ ∘ i ] ≡⟨ n ⟩ g → ⟨ f , g ⟩ ≡⟨ n ⟩ i
  ≈ₙ-univ {C} p q eq = let eq' = ≈ₙ-sym C eq in ≈ₙ-sym A (p eq') , ≈ₙ-sym B (q eq')

  .univ : ∀ {C} {f : Ofes [ C , A ]}{g : Ofes [ C , B ]}{i : Ofes [ C , A ×-ofe B ]} →
         Ofes [ Ofes [ π₁ ∘ i ] ≡ f ] → Ofes [ Ofes [ π₂ ∘ i ] ≡ g ] → Ofes [ ⟨ f , g ⟩ ≡ i ]
  univ {C}{f}{g}{i} p q {n} = ≈ₙ-univ {f = f}{g}{i = i} p q

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
  where open BinProd

products : ∀ {s₁ s₂ e} → Products (Ofes {s₁}{s₂}{e})
products = record {
  terminal = terminal ;
  binary = binary-products }

monoidal : ∀ {s₁ s₂ e} → Monoidal (Ofes {s₁}{s₂}{e})
monoidal = Cartesian Ofes products

open Cofe

-- taking products of cofes preserves completeness
infixr 2 _×-cofe_
_×-cofe_ : ∀ {o e e'}(A B : Cofe o e e') → Cofe o e e'
A ×-cofe B = record
  { ofe = (ofe A) ×-ofe (ofe B)
  ; conv = λ c →
    let
      l = conv A (chain-map (π₁ (ofe A) (ofe B)) c)
      r = Cofe.conv B (chain-map (π₂ (ofe A) (ofe B)) c)
    in lim (at-∞ l , at-∞ r) (λ n → limit l n , limit r n) }
  where open BinProd
