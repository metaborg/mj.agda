module Categorical.Ofe.Exponentials where

open import Data.Product
open import Relation.Binary.PropositionalEquality using () renaming (refl to ≣-refl)

open import Categorical.Ofe
open import Categorical.Ofe.Products

open import Categories.Category
open import Categories.Support.Equivalence
open import Categories.Object.BinaryProducts

module _ {ℓ} where
  open import Categories.Object.Exponential (Ofes {ℓ}{ℓ}{ℓ})
  open import Categories.Object.Product (Ofes {ℓ}{ℓ}{ℓ}) as Prod using (Product)
  open import Categories.Object.Product.Morphisms (Ofes {ℓ}{ℓ}{ℓ})
  open Product renaming (⟨_,_⟩ to _⟨_,_⟩)

  open Ofe
  open Exponential
  open Category (Ofes {ℓ}{ℓ}{ℓ})
  module Binary = BinaryProducts (binary-products {ℓ}{ℓ}{ℓ})

  eval' : ∀ {A B : Obj} → Ofes [ (A ⇨ B) ×-ofe A , B ]
  _⟨$⟩_ eval' (f , a)     = f ⟨$⟩ a
  cong eval'  (feq , aeq) = feq aeq

  λg' : ∀ {X A B} → (X×A : Product X A) → Ofes [ Product.A×B X×A , B ] → Ofes [ X , (A ⇨ B) ]
  _⟨$⟩_ (λg' {X}{A} X×A f) x = f ∘ Prod.repack Binary.product X×A ∘ Binary.⟨ const A X x , id ⟩
  cong  (λg' {X}{A} X×A f) {n}{x}{y} eq {a}{b} eq' = cong (f ∘ Prod.repack Binary.product X×A) (eq , eq')

  .β' : ∀ {X A B} → (X×A : Product X A) {g : Product.A×B X×A ⇒ B} →
       eval' ∘ [ X×A ⇒ Binary.product ]first (λg' X×A g) ≡ g
  β' {X}{A}{B} X×A {g} {x = x}{y} eq =
    begin
      eval' ∘ [ X×A ⇒ Binary.product ]first (λg' X×A g) ⟨$⟩ x
    ↓≣⟨ ≣-refl ⟩
      g ∘ (Prod.repack Binary.product X×A) ∘ (Prod.repack X×A Binary.product) ⟨$⟩ x
    ↓⟨ cong g (Prod.repack-cancel Binary.product X×A (≈ₙ-refl (A×B X×A))) ⟩
      g ⟨$⟩ x
    ↓⟨ cong g eq ⟩
      g ⟨$⟩ y
    ∎
    where open OfeReasoning B

  .λ-uniq : ∀ {X A B} → (X×A : Product X A)
      {g : Product.A×B X×A ⇒ B}
      {h : X ⇒ (A ⇨ B)} →
      eval' ∘ [ X×A ⇒ Binary.product ]first h ≡ g → h ≡ λg' X×A g
  λ-uniq {X}{A}{B} X×A {g}{h} eq {n}{x}{y} x≈y {u}{v} u≈v =
    begin
      h ⟨$⟩ x ⟨$⟩ u
    ↓⟨ cong h x≈y u≈v ⟩
      h ⟨$⟩ y ⟨$⟩ v
    ↑⟨ cong h (commute₁ X×A (≈ₙ-refl (X ×-ofe A))) (commute₂ X×A (≈ₙ-refl (X ×-ofe A))) ⟩
      h ⟨$⟩ ([ X×A ]π₁ ⟨$⟩ (Prod.repack Binary.product X×A ⟨$⟩ (y , v)))
        ⟨$⟩ ([ X×A ]π₂ ⟨$⟩ (Prod.repack Binary.product X×A ⟨$⟩ (y , v)))
    ↓≣⟨ ≣-refl ⟩
      eval' ∘ [ X×A ⇒ Binary.product ]first h  ∘ Prod.repack Binary.product X×A ∘ Binary.⟨ const A X y , id ⟩ ⟨$⟩ v
    ↓⟨ eq (≈ₙ-refl (A×B X×A)) ⟩
      (g ∘ Prod.repack Binary.product X×A ∘ Binary.⟨ const A X y , id ⟩ ⟨$⟩ v)
    ∎
    where open OfeReasoning B

  exp : ∀ A B → Exponential A B
  B^A      (exp A B) = A ⇨ B
  product  (exp A B) = Binary.product
  eval     (exp A B) = eval'
  λg       (exp A B) = λg'
  β        (exp A B) = β'
  λ-unique (exp A B) = λ-uniq
