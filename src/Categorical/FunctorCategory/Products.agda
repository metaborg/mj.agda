module Categorical.FunctorCategory.Products where

import Relation.Binary.PropositionalEquality as PEq

open import Level
open import Categories.Functor.Core
open import Categories.Category
open import Categories.Product
open import Categories.FunctorCategory
open import Categories.Object.BinaryProducts
open import Categories.Object.Product
open import Categories.Object.Products
open import Categories.Object.Terminal
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Monoidal
open import Categories.Monoidal.Cartesian

open import Categorical.Functor.Const

open Category
open NaturalTransformation

module _ {c ℓ e c' ℓ' e'}
  (C : Category c ℓ e)
  (D : Category c' ℓ' e')
  (prodD : Products D) where
  F = Functors C D

  module TerminalD = Terminal (Products.terminal prodD)

  terminal : Terminal F
  terminal = record {
    ⊤ = const TerminalD.⊤
    ; ! = λ {A} → record
      { η = λ X → TerminalD.!
      ; commute = λ f → let open HomReasoning D in
        (begin
          D [ TerminalD.! ∘ Functor.F₁ A f ]
        ↑⟨ TerminalD.!-unique (D [ TerminalD.! ∘ Functor.F₁ A f ]) ⟩
          TerminalD.!
        ↑⟨ identityˡ D ⟩
          D [ Category.id D ∘ TerminalD.! ]
        ∎)
      }
    ; !-unique = λ f → λ {x} → TerminalD.!-unique _ }

  open BinaryProducts using (product)
  prodF : BinaryProducts F
  product prodF {A}{B} = record
    { A×B = A×B
    ; π₁ = record
      { η = λ X → Prod.π₁
      ; commute = λ f → Prod.π₁∘⁂ }
    ; π₂ = record
      { η = λ X → Prod.π₂
      ; commute = λ f → Prod.π₂∘⁂ }
    ; ⟨_,_⟩ = λ {C} f g → record
      { η = λ X → Prod.⟨ η f X  , η g X ⟩
      ; commute = λ {X}{Y} h →
        let open HomReasoning D in
        begin
          D [ Prod.⟨ η f Y , η g Y ⟩ ∘ Functor.F₁ C h ]
        ↓⟨ Prod.⟨⟩∘ ⟩
          Prod.⟨ D [ η f Y ∘ Functor.F₁ C h ] , D [ η g Y ∘ Functor.F₁ C h ] ⟩
        ↓⟨ Prod.⟨⟩-cong₂ (commute f h) (commute g h) ⟩
          Prod.⟨ D [ (A.F₁ h) ∘ η f X ] , D [ B.F₁ h ∘ η g X ] ⟩
        ↑⟨ Prod.⁂∘⟨⟩ ⟩
          D [ (A.F₁ h Prod.⁂ B.F₁ h) ∘ Prod.⟨ η f X , η g X ⟩ ]
        ∎
      }
    ; commute₁ = λ {C₁} {f} {g} {x} → Prod.commute₁
    ; commute₂ = λ {C₁} {f} {g} {x} → Prod.commute₂
    ; universal = λ p q → Prod.universal p q }
    where
      private
        module A = Functor A
        module B = Functor B
        module Prod = BinaryProducts (Products.binary prodD)

      -- pointwise product
      A×B : Obj F
      A×B = record {
          F₀ = λ x → A.F₀ x Prod.× B.F₀ x
        ; F₁ = λ f → A.F₁ f Prod.⁂ B.F₁ f
        ; identity = λ {A₁} →
          let open HomReasoning D; open Equiv D in (
          begin
            A.F₁ (Category.id C) Prod.⁂ B.F₁ (Category.id C)
          ↓⟨ Prod.⁂-cong₂ (Functor.identity A) (Functor.identity B) ⟩
            Category.id D Prod.⁂ Category.id D
          ↓⟨ Prod.universal (trans (identityʳ D) (sym (identityˡ D))) (trans (identityʳ D) (sym (identityˡ D))) ⟩
            Category.id D
          ∎)
        ; homomorphism = λ {X} {Y} {Z} {f} {g} →
          let open HomReasoning D; open Equiv D in (
          begin
            A.F₁ (C [ g ∘ f ]) Prod.⁂ B.F₁ (C [ g ∘ f ])
          ↓⟨ Prod.⁂-cong₂ A.homomorphism B.homomorphism ⟩
            (D [ A.F₁ g ∘ A.F₁ f ]) Prod.⁂ (D [ B.F₁ g ∘ B.F₁ f ])
          ↑⟨ Prod.⁂∘⁂ ⟩
            D [ A.F₁ g Prod.⁂ B.F₁ g ∘ A.F₁ f Prod.⁂ B.F₁ f ]
          ∎)
        ; F-resp-≡ = λ {_}{_}{F}{G} F≡G → Prod.⁂-cong₂ (A.F-resp-≡ F≡G) (B.F-resp-≡ F≡G) }

  products : Products F
  products = record {
    terminal = terminal ;
    binary = prodF }

  monoidal : Monoidal F
  monoidal = Cartesian F products
