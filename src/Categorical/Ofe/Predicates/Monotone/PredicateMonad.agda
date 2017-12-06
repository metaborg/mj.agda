{-# OPTIONS --allow-unsolved-metas #-}
open import Categorical.Preorder
open import Categorical.Ofe.Predicates
open import Categories.Support.Equivalence

module Categorical.Ofe.Predicates.Monotone.PredicateMonad
  {ℓ}(preorder : PreorderPlus ℓ ℓ ℓ)
  (Pr : (PreorderPlus.Carrier preorder) → Set ℓ) where -- Pred (PreorderPlus.Carrier preorder) {ℓ}{ℓ}{ℓ}

open import Level

open import Data.Product hiding (∃-syntax)
open import Function as Fun using (case_of_;_∋_)
open import Relation.Binary.Core
open import Relation.Binary using (IsPreorder) renaming (Preorder to Po)
open import Relation.Binary.PropositionalEquality as PEq using () renaming (_≡_ to _≣_)

open import Categories.Category
open import Categories.Agda
open import Categories.Functor using (Functor; Endofunctor) renaming (id to 𝕀; _∘_ to _F∘_)
open import Categories.Monad
open import Categories.Monad.Strong
open import Categories.NaturalTransformation using (NaturalTransformation; _∘₀_; _∘₁_; _∘ˡ_; _∘ʳ_)
open import Categories.Support.EqReasoning

open import Categorical.Ofe
open import Categorical.Ofe.Products
open import Categorical.Ofe.Predicates.Closures
open import Categorical.Ofe.Predicates.Monotone preorder

open PreorderPlus preorder using () renaming (Carrier to Shape)
open NaturalTransformation using (η; commute)
open Category
open Functor
open Ofe

private
  module MP = Category (MP {ℓ}{ℓ}{ℓ})
  Ord = Category.op (PreorderPlus.Ord preorder)
  module Ord = Category Ord

module Result where

  -- Morally : (X ≤ Y × Pr Y) × P Y
  -- This isn't a monotone predicate... (it is anti-monotone in X)
  Result : Shape → Pred Shape {ℓ}{ℓ}{ℓ} → Pred Shape
  Result X P Y = (Δ (Ord.hom-setoid {X}{Y}) ×-ofe Δ⁺ (Pr Y)) ×-ofe (P Y)

  result-map : ∀ {X : Shape}(P Q : Pred Shape) →
               (f : Preds Shape [ P , Q ]) → Preds Shape [ Result X P , Result X Q ]
  result-map {X} P Q f = record
    { _⟨$⟩_ = λ x → proj₁ x , f ⟨$⟩ (proj₂ x)
    ; cong  = λ x → proj₁ x , cong f (proj₂ x) }

  -- But it should be an endofunctor of carrier indexed setoids.
  ResF : Shape → Functor (Preds Shape) (Preds Shape)
  F₀ (ResF Σ) = Result Σ
  F₁ (ResF Σ) = result-map _ _
  identity (ResF Σ) {A}{Σ'} = (refl , refl) , ≈ₙ-refl (A Σ')
  homomorphism (ResF Σ){P}{Q}{R}{Σ = Σ'} = (refl , refl) , ≈ₙ-refl (R Σ')
  F-resp-≡ (ResF Σ) F≡G = (refl , refl) , F≡G

module PredicateT (M : Monad (Ofes {ℓ}{ℓ}{ℓ})) where

  open Result
  open Monad M using () renaming (F to F)

  private
    module M = Monad M
    module F = Functor F

  -- ∃ λ (X' : Shape) → X' ≥ X × Pr X' × P X'
  ∃Result : Shape → Pred Shape → Ofe ℓ ℓ ℓ
  ∃Result X P = ∃[ Shape ] (Result X P)

  -- ∃Result is an anti-monotone predicate
  -- for now we'll do with the following lemma
  result-anti : ∀ {X Y}(P : Pred Shape) → Ord [ X , Y ] → ∃Result Y P ⟶ ∃Result X P
  _⟨$⟩_ (result-anti P X⇒Y) (Z , (Y⇒Z , μ) , px) = Z , (Ord [ Y⇒Z ∘ X⇒Y ] , μ) , px
  cong (result-anti P X⇒Y) (hrefl ((refl , eq) , eq')) = hrefl ((refl , eq) , eq')

  .result-anti-id : ∀ {X}(P : Pred Shape) → Ofes [ result-anti {X = X} P (id Ord) ≡ id Ofes ]
  result-anti-id P (hrefl ((refl , eq) , eq')) = hrefl ((Ord.identityʳ , eq) , eq')

  -- object mapping
  -- omap P Σ ≡morally≡ ∀ Σ' → Σ' ≥ Σ → Pr Σ' → M (∃ λ Σ'' → Σ'' ≥ Σ' × Pr Σ'' × P Σ'')
  omap : (P : MP.Obj) → MP.Obj
  omap P = ∀[ preorder ]≤ PredicateFun
    module omap where
      module P = Functor P

      PredicateFun : Shape → Ofe _ _ _
      PredicateFun X =
        ∀[ Pr X ] λ μ → F₀ (Monad.F M) (∃Result X P.F₀)

  open omap

  map-∃ : ∀ {A B c} → (MP [ A , B ]) → Ofes [ ∃Result c (F₀ A) , ∃Result c (F₀ B) ]
  _⟨$⟩_ (map-∃ A⇒B) (Σ , S , v) = Σ , S , (η A⇒B Σ) ⟨$⟩ v
  cong (map-∃ {A} {B} A⇒B) = ≅⟨⟩-cong (result-map (F₀ A) (F₀ B) (η A⇒B _))

  hmap : ∀ {A B : MP.Obj} → MP [ A , B ] → MP [ omap A , omap B ]
  _⟨$⟩_ (η (hmap A⇒B) X) φ    C X⇒C μ = F.F₁ (map-∃ A⇒B) ⟨$⟩ (φ C X⇒C μ)
  cong (η (hmap A⇒B) X) φ≡φ' C X⇒C μ = F.F-resp-≡ (cong (map-∃ A⇒B)) (φ≡φ' C X⇒C μ)
  commute (hmap {A} {B} A⇒B) {X = X}{Y} X⇒Y {n}{x} {y} x≡y =
    begin
      Ofes [ η (hmap A⇒B) Y ∘ (F₁ (omap A) X⇒Y) ] ⟨$⟩ x
    ↓⟨ cong (Ofes [ η (hmap A⇒B) Y ∘ (F₁ (omap A) X⇒Y) ]) x≡y ⟩
      Ofes [ η (hmap A⇒B) Y ∘ (F₁ (omap A) X⇒Y) ] ⟨$⟩ y
    ↓⟨ ≈ₙ-refl (F₀ (omap B) Y) ⟩
      Ofes [ F₁ (omap B) X⇒Y ∘ (η (hmap A⇒B) X) ] ⟨$⟩ y ∎
    where open OfeReasoning (F₀ (omap B) Y)

  .homomorphism' : ∀ {X Y Z : Obj MP}(f : MP [ X , Y ])(g : MP [ Y , Z ]) →
                   MP [ hmap (MP [ g ∘ f ]) ≡ MP [ hmap g ∘ hmap f ] ]
  homomorphism' {P}{Q}{R} F G {x = X}{_}{f}{g} f≡g C X⇒C μ =
    begin
      F.F₁ (map-∃ (MP [ G ∘ F ])) ⟨$⟩ f C X⇒C μ
    ↓⟨ F.homomorphism (f≡g C X⇒C μ) ⟩
      F.F₁ (map-∃ G) ⟨$⟩ (F.F₁ (map-∃ F) ⟨$⟩ g C X⇒C μ)
    ↓≣⟨ refl ⟩
      ((η (MP [ hmap G ∘ hmap F ]) X ⟨$⟩ g)) C X⇒C μ ∎
    where open OfeReasoning (F.F₀ (∃Result C (F₀ R)))

  .resp-≡ : {P Q : Obj MP}(F G : MP [ P , Q ]) → MP [ F ≡ G ] → MP [ hmap F ≡ hmap G ]
  resp-≡ {P}{Q} F G F≡G {_}{_}{f}{g} f≡g Y X⇒Y μY =
    begin
      F.F₁ (map-∃ F) ⟨$⟩ f Y X⇒Y μY
    ↓⟨ cong (F.F₁ (map-∃ F)) (f≡g Y X⇒Y μY) ⟩
      F.F₁ (map-∃ F) ⟨$⟩ g Y X⇒Y μY
    ↓⟨ F.F-resp-≡ (λ{ (hrefl (eq , eq')) → hrefl (eq , F≡G eq')}) (≈ₙ-refl (F.F₀ (∃Result Y (F₀ P)))) ⟩
      F.F₁ (map-∃ G) ⟨$⟩ g Y X⇒Y μY ∎
    where open OfeReasoning (F.F₀ (∃Result Y (F₀ Q)))

  .identity′ : ∀ {P} → MP [ hmap {P} MP.id ≡ MP.id ]
  identity′ f≡g C X⇒C μ = F.identity (f≡g C X⇒C μ)

  functor : Endofunctor MP
  functor = record
    {F₀ = omap
    ; F₁ = hmap
    ; identity = λ {P} → identity′ {P}
    ; homomorphism = λ{ {f = f}{g} → homomorphism' f g }
    ; F-resp-≡ = λ{ {F = F}{G} → resp-≡ F G }}

  return : ∀ (P : Obj MP) → MP [ P , omap P ]
  _⟨$⟩_ (η (return P) X) x Y X⇒Y μ = η M.η _ ⟨$⟩ (Y , (id Ord , μ) , (F₁ P X⇒Y) ⟨$⟩ x)
  cong (η (return P) X) i≡j Y X⇒Y μ = cong (η M.η _) (hrefl ((refl , refl) , cong (F₁ P X⇒Y) i≡j ))
  commute (return P) {X}{Y} X⇒Y {_}{x}{y} x≡y Z Y⇒Z μZ =
    begin
      (Ofes [ η (return P) Y ∘ (F₁ P X⇒Y) ] ⟨$⟩ x) Z Y⇒Z μZ
    ↓≣⟨ refl ⟩
      η M.η _ ⟨$⟩ (Z , (id Ord , μZ) , F₁ P Y⇒Z ⟨$⟩ (F₁ P X⇒Y ⟨$⟩ x))
    ↑⟨ cong (η M.η _) (hrefl ((refl , refl) , homomorphism P (≈ₙ-sym (F₀ P X) x≡y))) ⟩
      η M.η _ ⟨$⟩ (Z , (id Ord , μZ) , F₁ P (Ord [ X⇒Y ∘ Y⇒Z ]) ⟨$⟩ y)
    ↓≣⟨ refl ⟩
      (Ofes [ F₁ (omap P) X⇒Y ∘ (η (return P) X) ] ⟨$⟩ y) Z Y⇒Z μZ ∎
    where open OfeReasoning (F.F₀ (∃Result Z (F₀ P)))

  private
    collapse : ∀ P {Y} → Ofes [ ∃Result Y (F₀ (omap P)) , F.F₀ (∃Result Y (F₀ P)) ]
    _⟨$⟩_ (collapse P) (Y , (X⇒Y , μ) , f) =
      F.F₁ (result-anti (F₀ P) X⇒Y) ⟨$⟩ (f Y (id Ord) μ)
    cong  (collapse P) {_}{Σ , (X⇒Y , μ) , v} (hrefl ((refl , refl) , eq)) =
      F.F-resp-≡ (cong (result-anti (F₀ P) X⇒Y)) (eq Σ (id Ord) μ)

    .collapse-return : ∀ {P} Y → Ofes [ (Ofes [ collapse P {Y} ∘ (map-∃ (return P)) ]) ≡ η M.η _ ]
    collapse-return {P} Y {_}{(Σ , (X⇒Y , μ) , v)}{y} x≡y =
      begin
        F.F₁ (result-anti (F₀ P) X⇒Y) ⟨$⟩ (η M.η _ ⟨$⟩ (Σ , (id Ord , μ) , (F₁ P (id Ord)) ⟨$⟩ v))
      ↑⟨ commute M.η (result-anti (F₀ P) X⇒Y) (≈ₙ-refl (∃Result Σ (F₀ P))) ⟩
        η M.η _ ⟨$⟩ ((result-anti (F₀ P) X⇒Y) ⟨$⟩ (Σ , (id Ord , μ) , (F₁ P (id Ord)) ⟨$⟩ v))
      ↓⟨ cong (η M.η _) (hrefl (((identityˡ Ord) , refl) , identity P (≈ₙ-refl (F₀ P _)))) ⟩
        η M.η _ ⟨$⟩ (Σ , (X⇒Y , μ) , v)
      ↓⟨ cong (η M.η _) x≡y ⟩
        η M.η _ ⟨$⟩ y
      ∎
      where open OfeReasoning (F.F₀ (∃Result Y (F₀ P)))

    .anti-map-∃-comm : ∀ {P Q : Obj MP}{X Y} (X⇒Y : Ord [ X , Y ]) (P⇒Q : MP [ P , Q ]) →
                       Ofes [ (Ofes [ result-anti (F₀ Q) X⇒Y ∘ (map-∃ P⇒Q) ]) ≡
                              (Ofes [ map-∃ P⇒Q ∘ (result-anti (F₀ P) X⇒Y) ]) ]
    anti-map-∃-comm {P}{Q}{X}{Y} X⇒Y P⇒Q {_}{(Z , (Y⇒Z , μ), v)}{y} x≡y =
      cong (map-∃ P⇒Q) (cong (result-anti (F₀ P) X⇒Y) x≡y)

    .collapse-lem : ∀ {P Q}(P⇒Q : MP [ P , Q ]) Y →
                    Ofes [
                      Ofes [ collapse Q {Y} ∘ map-∃ (hmap P⇒Q) ] ≡
                      Ofes [ F.F₁ (map-∃ P⇒Q) ∘ collapse P ]
                    ]
    collapse-lem {P} {Q} P⇒Q Y {_}{x}{(X , (X⇒Y , μ) , f)} x≡y =
      begin
        collapse Q ⟨$⟩ (map-∃ (hmap P⇒Q) ⟨$⟩ x)
      ↓⟨ cong (collapse Q) (cong (map-∃ (hmap P⇒Q)) x≡y) ⟩
        collapse Q ⟨$⟩ (map-∃ (hmap P⇒Q) ⟨$⟩ (X , (X⇒Y , μ) , f))
      ↓≣⟨ refl ⟩
        F.F₁ (result-anti (F₀ Q) X⇒Y) ⟨$⟩ ((η (hmap P⇒Q) X ⟨$⟩ f) X (id Ord) μ)
      ↓≣⟨ refl ⟩
        F.F₁ (result-anti (F₀ Q) X⇒Y) ⟨$⟩ (F.F₁ (map-∃ P⇒Q) ⟨$⟩ (f X (id Ord) μ))
      ↑⟨ F.homomorphism (≈ₙ-refl (F.F₀ (∃Result X (F₀ P)))) ⟩
        F.F₁ (Ofes [ result-anti (F₀ Q) X⇒Y ∘ (map-∃ P⇒Q) ]) ⟨$⟩ (f X (id Ord) μ)
      ↓⟨ F.F-resp-≡ (anti-map-∃-comm X⇒Y P⇒Q) (≈ₙ-refl (F.F₀ (∃Result X (F₀ P)))) ⟩
        F.F₁ (Ofes [ map-∃ P⇒Q ∘ (result-anti (F₀ P) X⇒Y) ]) ⟨$⟩ (f X (id Ord) μ)
      ↓⟨ F.homomorphism (≈ₙ-refl (F.F₀ (∃Result X (F₀ P)))) ⟩
        F.F₁ (map-∃ P⇒Q) ⟨$⟩ (F.F₁ (result-anti (F₀ P) X⇒Y) ⟨$⟩ (f X (id Ord) μ))
      ↓≣⟨ refl ⟩
        F.F₁ (map-∃ P⇒Q) ⟨$⟩ (collapse P ⟨$⟩ (X , (X⇒Y , μ) , f))
      ∎
      where open OfeReasoning (F.F₀ (∃Result Y (F₀ Q)))

    ηjoin : ∀ P → Preds Shape [ (F₀ (omap (omap P))) , (F₀ (omap P)) ]
    _⟨$⟩_ (ηjoin P) f Y X⇒Y μY =
      Ofes [ η M.μ _ ∘ (F.F₁ (collapse P)) ] ⟨$⟩ (f Y X⇒Y μY)
    cong (ηjoin P){x = x}{y} x≡y Y X⇒Y μY =
      cong (η M.μ _) (cong (F.F₁ (collapse P)) (x≡y Y X⇒Y μY))

  join : ∀ (P : Obj MP) → MP [ omap (omap P) , omap P ]
  (η (join P) X) = ηjoin P
  commute (join P) {X}{Y} X⇒Y {_}{x}{y} x≡y =
    begin
      (Ofes [ η (join P) Y ∘ (F₁ (omap (omap P)) X⇒Y)] ⟨$⟩ x)
    ↓⟨ cong (Ofes [ η (join P) Y ∘ (F₁ (omap (omap P)) X⇒Y)]) x≡y ⟩
      (Ofes [ η (join P) Y ∘ (F₁ (omap (omap P)) X⇒Y)] ⟨$⟩ y)
    ↓≣⟨ refl ⟩
      (Ofes [ F₁ (omap P) X⇒Y ∘ (η (join P) X) ] ⟨$⟩ y)
    ∎
    where open OfeReasoning (F₀ (omap P) Y)

  open Monad
  open Functor

  monad : Monad MP
  F monad = functor

  -- natural return
  η (η monad) = return
  commute (η monad) {P}{Q} P⇒Q {X}{_}{x}{y} x≡y =
    begin
      (η (MP [ (return Q) ∘ P⇒Q ]) X ⟨$⟩ x)
    ↓⟨ cong (η (MP [ return Q ∘ P⇒Q ]) X) x≡y ⟩
      (η (return Q) X) ⟨$⟩ (η P⇒Q X ⟨$⟩ y)
    ↓≣⟨ refl ⟩
      (λ Y X⇒Y μ → η M.η _ ⟨$⟩ (Y , (id Ord , μ) , (F₁ Q X⇒Y) ⟨$⟩ (η P⇒Q X ⟨$⟩ y)))
    ↑⟨ (λ Y F μ → cong (η M.η _) (hrefl ((refl , refl) , commute P⇒Q F (≈ₙ-refl (F₀ P X))))) ⟩
      (λ Y X⇒Y μ → η M.η _ ⟨$⟩ (Y , (id Ord , μ) , η P⇒Q Y ⟨$⟩ ((F₁ P X⇒Y) ⟨$⟩ y)))
    ↓≣⟨ refl ⟩
      (λ Y X⇒Y μ → η M.η _ ⟨$⟩ ((map-∃ P⇒Q) ⟨$⟩ (Y , (id Ord , μ) , (F₁ P X⇒Y) ⟨$⟩ y)))
    ↓⟨ (λ Y X⇒Y μ → commute M.η (map-∃ P⇒Q) (hrefl ((refl , refl) , (≈ₙ-refl (F₀ P Y))))) ⟩
      (η (hmap P⇒Q) X) ⟨$⟩ (λ Y X⇒Y μ → (η M.η _ ⟨$⟩ (Y , (id Ord , μ) , (F₁ P X⇒Y) ⟨$⟩ y)))
    ↓≣⟨ refl ⟩
      (η (hmap P⇒Q) X) ⟨$⟩ (η (return P) X ⟨$⟩ y)
    ∎
    where
      open OfeReasoning (F₀ (omap Q) X)

  -- natural join
  η (μ monad) = join
  commute (μ monad) {P} {Q} P⇒Q {X} {_}{x}{y} x≡y Y X⇒Y μY =
    begin
      (η (join Q MP.∘ (hmap (hmap P⇒Q))) X ⟨$⟩ x) Y X⇒Y μY
    ↓⟨ (cong (η (join Q MP.∘ (hmap (hmap P⇒Q))) X) x≡y) Y X⇒Y μY ⟩
      (η (join Q MP.∘ (hmap (hmap P⇒Q))) X ⟨$⟩ y) Y X⇒Y μY
    ↓≣⟨ refl ⟩
      (Ofes [ η M.μ _ ∘ F.F₁ (collapse Q) ]) ⟨$⟩ ((η (hmap (hmap P⇒Q)) X ⟨$⟩ y) Y X⇒Y μY)
    ↓≣⟨ refl ⟩
      (η M.μ _ ⟨$⟩ ((F.F₁ (collapse Q)) ⟨$⟩ (F.F₁ (map-∃ (hmap P⇒Q)) ⟨$⟩ (y Y X⇒Y μY))))
    ↑⟨ cong (η M.μ _) (F.homomorphism (≈ₙ-refl (F.F₀ (∃Result Y (F₀ (omap P)))))) ⟩
      η M.μ _ ⟨$⟩ (F.F₁ (Ofes [ collapse Q  ∘ (map-∃ (hmap P⇒Q)) ]) ⟨$⟩ (y Y X⇒Y μY))
    ↓⟨ cong (η M.μ _) (F.F-resp-≡ (collapse-lem P⇒Q Y) (≈ₙ-refl (F.F₀ (∃Result Y (F₀ (omap P)))))) ⟩
      η M.μ _ ⟨$⟩ (F.F₁ (Ofes [ F.F₁ (map-∃ P⇒Q) ∘ collapse P ]) ⟨$⟩ (y Y X⇒Y μY))
    ↓⟨ cong (η M.μ _) (F.homomorphism (≈ₙ-refl (F.F₀ (∃Result Y (F₀ (omap P)))))) ⟩
      η M.μ _ ⟨$⟩ (F.F₁ (F.F₁ (map-∃ P⇒Q)) ⟨$⟩ (F.F₁ (collapse P) ⟨$⟩ y Y X⇒Y μY))
    ↓⟨ commute M.μ (map-∃ P⇒Q) (≈ₙ-refl (F₀ (M.F F∘ M.F) (∃Result Y (F₀ P)))) ⟩
      F.F₁ (map-∃ P⇒Q) ⟨$⟩ (η M.μ _ ⟨$⟩ (F.F₁ (collapse P) ⟨$⟩ y Y X⇒Y μY))
    ↓≣⟨ refl ⟩
      F.F₁ (map-∃ P⇒Q) ⟨$⟩ ((Ofes [ η M.μ _ ∘ F.F₁ (collapse P) ]) ⟨$⟩ y Y X⇒Y μY)
    ↓≣⟨ refl ⟩
      (η (hmap P⇒Q MP.∘ join P) X ⟨$⟩ y) Y X⇒Y μY
    ∎
    where
      open OfeReasoning (F.F₀ (∃Result Y (F₀ Q)))

  assoc monad {P}{Σ}{x = x}{y} x≡y Y Σ⇒Y μY =
    begin
      ((η (η (μ monad) P) Σ) ⟨$⟩ ((η (F₁ functor (η (μ monad) P)) Σ) ⟨$⟩ x)) Y Σ⇒Y μY
    ↓⟨ cong (η (η (μ monad ∘₁ functor ∘ˡ μ monad) P) Σ) x≡y Y Σ⇒Y μY ⟩
      ((η (η (μ monad) P) Σ) ⟨$⟩ ((η (F₁ functor (η (μ monad) P)) Σ) ⟨$⟩ y)) Y Σ⇒Y μY
    ↓⟨ {!!} ⟩
      ((η (η (μ monad) P) Σ) ⟨$⟩ (η (η (μ monad) (F₀ functor P)) Σ ⟨$⟩ y)) Y Σ⇒Y μY
    ∎
    where open OfeReasoning (F.F₀ (∃Result Y (F₀ P)))

  identityˡ monad {P}{Σ}{_}{x}{y} x≡y Y X⇒Y μY =
    begin
      (η M.μ (∃Result Y (F₀ P))) ⟨$⟩ (F.F₁ (collapse P) ⟨$⟩ (F.F₁ (map-∃ (return P)) ⟨$⟩ x Y X⇒Y μY))
    ↑⟨ (cong (η M.μ (∃Result Y (F₀ P))) (F.homomorphism (≈ₙ-refl (F.F₀ (∃Result Y (F₀ P)))))) ⟩
      (η M.μ (∃Result Y (F₀ P))) ⟨$⟩ (F.F₁ (Ofes [ collapse P ∘ (map-∃ (return P)) ]) ⟨$⟩ x Y X⇒Y μY)
    ↓⟨ cong (η M.μ (∃Result Y (F₀ P))) (F.F-resp-≡ (collapse-return {P} Y) (≈ₙ-refl (F.F₀ (∃Result Y (F₀ P))))) ⟩
      (η M.μ (∃Result Y (F₀ P))) ⟨$⟩ (F.F₁ (η M.η _) ⟨$⟩ x Y X⇒Y μY)
    ↓⟨ M.identityˡ (x≡y Y X⇒Y μY) ⟩
      y Y X⇒Y μY
    ∎
    where open OfeReasoning (F.F₀ (∃Result Y (F₀ P)))

  identityʳ monad {P}{Σ}{_}{x}{y} x≡y Y X⇒Y μY =
    begin
       (η M.μ _ ⟨$⟩ ((F.F₁ (collapse P)) ⟨$⟩ ((η (return (F₀ functor P)) Σ ⟨$⟩ x) Y X⇒Y μY)))
    ↓≣⟨ refl ⟩
       (η M.μ _ ⟨$⟩ ((F.F₁ (collapse P)) ⟨$⟩ (η M.η _ ⟨$⟩ (Y , (id Ord , μY) , (F₁ (F₀ functor P) X⇒Y) ⟨$⟩ x))))
    ↑⟨ cong (η M.μ _) (commute M.η (collapse P) (≈ₙ-refl (∃Result Y (F₀ (omap P))))) ⟩
       (η M.μ _ ⟨$⟩ (η M.η _ ⟨$⟩ (collapse P ⟨$⟩ (Y , (id Ord , μY) , (F₁ (F₀ functor P) X⇒Y) ⟨$⟩ x))))
    ↓≣⟨ refl ⟩
       (η M.μ _ ⟨$⟩ (η M.η _ ⟨$⟩ (F.F₁ (result-anti (F₀ P) (id Ord)) ⟨$⟩ (((F₁ (F₀ functor P) X⇒Y) ⟨$⟩ x) Y (id Ord) μY))))
    ↓⟨ cong (η M.μ _) (cong (η M.η _) (F.F-resp-≡ (result-anti-id (F₀ P)) (≈ₙ-refl (F.F₀ (∃Result Y (F₀ P)))))) ⟩
       (η M.μ _ ⟨$⟩ (η M.η _ ⟨$⟩ (F.F₁ (id (Ofes)) ⟨$⟩ (((F₁ (F₀ functor P) X⇒Y) ⟨$⟩ x) Y (id Ord) μY))))
    ↓⟨ cong (η M.μ _) (cong (η M.η _) (F.identity (≈ₙ-refl (F.F₀ (∃Result Y (F₀ P)))))) ⟩
       (η M.μ _ ⟨$⟩ (η M.η _ ⟨$⟩ (x Y (Ord [ X⇒Y ∘ id Ord ]) μY)))
    ↓⟨ cong (η M.μ _) (cong (η M.η _) (≈ₙ-reflexive (F.F₀ (∃Result Y (F₀ P))) (PEq.cong (λ u → x Y u μY) (PreorderPlus.unique preorder _ _)) _)) ⟩
       (η M.μ _ ⟨$⟩ (η M.η _ ⟨$⟩ x Y X⇒Y μY))
    ↓⟨ M.identityʳ (x≡y Y X⇒Y μY) ⟩
      y Y X⇒Y μY
    ∎
    where open OfeReasoning (F.F₀ (∃Result Y (F₀ P)))

  {-
  -- The monad is strong in this category
  strong : Strength MP monoidal St
  strong = record
    { σ = {!!}
    ; identity₁ = {!!}
    ; identity₂ = {!!}
    ; α-assoc = {!!}
    ; μ-assoc = {!!}
    }
  -}

open PredicateT using () renaming (monad to PredicateT) public

open import Categorical.Monad.Identity
Predicate :  Monad MP
Predicate = PredicateT.monad (idM _)
