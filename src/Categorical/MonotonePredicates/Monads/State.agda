{-# OPTIONS --show-implicit #-}
open import Categorical.Preorder

module Categorical.MonotonePredicates.Monads.State {ℓ ℓ₂}
  (po : PreorderPlus ℓ ℓ₂ ℓ)
  (Store : PreorderPlus.Carrier po → Set ℓ) where

open import Categorical.MonotonePredicates po
open PreorderPlus po hiding (po; assoc) renaming (Carrier to Shape)

open import Level

open import Data.Product
open import Function as Fun using (case_of_;_∋_)
open import Relation.Binary.PropositionalEquality as PEq using () renaming (_≡_ to _≣_)
open import Relation.Binary.HeterogeneousEquality as HEq using () renaming (_≅_ to _≡~_)

open import Categories.Category
open import Categories.Agda
open import Categories.Functor using (Functor; Endofunctor)
open import Categories.Monad
open import Categories.Monad.Strong
open import Categories.Support.Equivalence
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Support.SetoidFunctions as SF hiding (id)
open import Categories.Support.EqReasoning

open NaturalTransformation using (η; commute)
open Category
open Setoid
open Functor

private
  module MP = Category MP
  C = Category.op (Preorder po)

-- A category of *shape-indexed* setoids (≡ predicates on shapes)
module IndexedSetoid where

  -- alternative syntax for setoid equality
  _[_≈_] : ∀ {s₁ s₂} (S : Setoid s₁ s₂) → Carrier S → Carrier S → Set _
  _[_≈_] = Setoid._≈_

  Pred : ∀ s₁ s₂ → Category _ _ _
  Obj (Pred s₁ s₂) = (c : Shape) → Setoid s₁ s₂
  _⇒_ (Pred s₁ s₂) T S = ∀ {Σ} → (T Σ) ⟶ (S Σ)
  _≡_ (Pred s₁ s₂) {A}{B} f g = ∀ {Σ}{x : Carrier (A Σ)} → Setoid._≈_ (B Σ) (f ⟨$⟩ x) (g ⟨$⟩ x)
  id (Pred s₁ s₂) = SF.id
  _∘_ (Pred s₁ s₂) f g = f ∙ g
  assoc (Pred s₁ s₂) {A} {B} {C} {D} = Setoid.refl (D _)
  identityˡ (Pred s₁ s₂) {A} {B} = Setoid.refl (B _)
  identityʳ (Pred s₁ s₂) {A} {B} = Setoid.refl (B _)
  equiv (Pred s₁ s₂) {A}{B} = record
      { refl = Setoid.refl (B _)
      ; sym = λ eq → sym (B _) eq
      ; trans = λ eq₁ eq₂ → Setoid.trans (B _) eq₁ eq₂ }
  ∘-resp-≡ (Pred s₁ s₂) {A}{B}{C}{f}{g}{h}{i} f≡g h≡i {Σ}{x} =
    begin
      f ⟨$⟩ (h ⟨$⟩ x)
        ↓⟨ cong f h≡i ⟩
      f ⟨$⟩ (i ⟨$⟩ x)
        ↓⟨ f≡g ⟩
      g ⟨$⟩ (i ⟨$⟩ x) ∎
    where open SetoidReasoning (C Σ)

  Pred' : ∀ {s₁ s₂} → Category _ _ _
  Pred' {s₁} {s₂} = Pred s₁ s₂

  -- lift equality indexed-setoid into a heterogeneous equality type
  data _[_≅_] {s₁ s₂}(I : Obj (Pred s₁ s₂)) {c} : ∀ {c'} → Carrier (I c) → Carrier (I c') → Set (ℓ ⊔ s₁ ⊔ s₂) where
    hrefl : ∀ {l r} → (I c) [ l ≈ r ] → I [ l ≅ r ]

  .≅cong : ∀ {s₁ s₂}{I J : Obj (Pred s₁ s₂)}
            {l l'}{r : Carrier (I l)}{r' : Carrier (I l')} →
            (f : Pred' [ I , J ]) → I [ r ≅ r' ] → J [ (f ⟨$⟩ r) ≅ (f ⟨$⟩ r') ]
  ≅cong f (hrefl x) = (hrefl (cong f x))

  ∃[_]-setoid_ : ∀ {ℓ s₁ s₂} → (A : Set ℓ) → Obj (Pred s₁ s₂) → Setoid _ _
  ∃[ A ]-setoid B = record
    { Carrier = ∃ λ a → B.Carrier a
    ; _≈_ = λ p q → B [ (proj₂ p) ≅ (proj₂ q) ]
    ; isEquivalence = record {
      refl = λ {x} → hrefl (Setoid.refl (B (proj₁ x))) ;
      sym = λ{ {i}{j}(hrefl p) → hrefl (Setoid.sym (B (proj₁ j)) p) };
      trans = λ{ (hrefl p) (hrefl q) → hrefl (Setoid.trans (B _) p q) }}
    }
    where module B a = Setoid (B a)

module Result where

  open IndexedSetoid

  -- Morally : (X ≤ Y × State Y) × P Y
  -- This isn't a monotone predicate... (I think it's anti-monotone in X) -- Arjen
  Result : ∀ {s₁ s₂} → Shape → Obj (Pred s₁ s₂) → Obj (Pred _ _)
  Result X P Y = (set→setoid (C [ X , Y ] × Store Y)) ×-setoid (P Y)

  result-map : ∀ {s₁ s₂}{X : Shape}(P Q : Obj (Pred s₁ s₂)) →
              (f : Pred' [ P , Q ]) → Pred' [ Result X P , Result X Q ]
  result-map {X}{Y} P Q f = record
    { _⟨$⟩_ = λ x → proj₁ x , f ⟨$⟩ (proj₂ x)
    ; cong  = λ x → proj₁ x , cong f (proj₂ x) }

  -- But it should be an endofunctor of carrier indexed setoids.
  ResF : ∀ {s₁ s₂} → Shape → Functor (Pred s₁ s₂) (Pred _ _)
  F₀ (ResF Σ) = Result Σ
  F₁ (ResF Σ) = result-map _ _
  identity (ResF Σ) {A}{Σ'} = PEq.refl , Setoid.refl (A Σ')
  homomorphism (ResF {s₁}{s₂}Σ){P}{Q}{R}{Σ = Σ'} = PEq.refl , Setoid.refl (R Σ')
  F-resp-≡ (ResF Σ) F≡G = PEq.refl , F≡G

module State where

  open Result
  open IndexedSetoid

  ∃Result : ∀ {s₁ s₂} → Shape → Obj (Pred s₁ s₂) → Setoid _ _
  ∃Result Σ P = ∃[ Shape ]-setoid (Result Σ P)

  omap : (P : MP.Obj) → MP.Obj
  omap P = ∀-closure[ StateFun ]
    module omap where
      module P = Functor P

      -- fmap-result : ∀ {X} → (MP [ A ⇒ B ])
      StateFun : Shape → Setoid ℓ ℓ
      StateFun X =
        ∀[ Store X ]-setoid λ μ →
        ∃Result X P.F₀

  open omap

  hmap : ∀ {A B : MP.Obj} → MP [ A , B ] → MP [ omap A , omap B ]
  _⟨$⟩_ (η (hmap A⇒B) X) φ C X⇒C μ =
    let
      (Σ , S , v) = φ _ X⇒C μ
    in Σ , S , (η A⇒B Σ) ⟨$⟩ v
  cong (η (hmap {A}{B} A⇒B) X) φ≡φ' C X⇒C μ = ≅cong (result-map (F₀ A) (F₀ B) (η A⇒B _)) (φ≡φ' C X⇒C μ)
  commute (hmap {A} {B} A⇒B) X⇒Y {x} {y} x≡y Z Y⇒Z μZ =
    let
      X⇒Z = C [ Y⇒Z ∘ X⇒Y ]
      (Z₁ , S , v) = x _ X⇒Z μZ
      (Z₂ , S' , w) = y _ X⇒Z μZ
    in
      begin
        Z₁ , S , (η A⇒B _) ⟨$⟩ v
          ≈⟨ ≅cong (result-map (F₀ A) (F₀ B) (η A⇒B _)) (x≡y Z X⇒Z μZ) ⟩
        Z₂ , S' , (η A⇒B _) ⟨$⟩ w ∎
    where open SetoidReasoning (∃Result Z (F₀ B))

  return : ∀ (P : Obj MP) → MP [ P , omap P ]
  _⟨$⟩_ (η (return P) X) x Y X⇒Y μ = Y , (id C , μ) , (F₁ P X⇒Y) ⟨$⟩ x
  cong (η (return P) X) i≡j Y X⇒Y μ = (hrefl (PEq.refl , cong (F₁ P X⇒Y) i≡j ))
  commute (return P) {X}{Y} X⇒Y {x}{y} x≡y Z Y⇒Z μZ =
    begin
      (Z , (id C , μZ) , F₁ P Y⇒Z ⟨$⟩ (F₁ P X⇒Y ⟨$⟩ x))
      ↑⟨ hrefl (PEq.refl , homomorphism P (Setoid.sym (F₀ P X) x≡y)) ⟩
      (Z , (id C , μZ) , F₁ P (C [ Y⇒Z ∘ X⇒Y ]) ⟨$⟩ y)
      ↑≣⟨ PEq.refl ⟩
      ((F₁ (omap P) X⇒Y ⟨$⟩ (λ Y₁ X⇒Y₁ μ → Y₁ , (id C , μ) , F₁ P X⇒Y₁ ⟨$⟩ y)) Z Y⇒Z μZ)
    ∎
    where open SetoidReasoning (∃Result Z (F₀ P))

  private
    combine : ∀ P {X} →
              (v : Carrier (∃Result X (F₀ (omap P)))) →
              Carrier (∃Result (proj₁ v) (F₀ P)) →
              Carrier (∃Result X (F₀ P))
    combine P (Y , (X⇒Y , μY) , f) (Z , (Y⇒Z , μZ) , v) = Z , (C [ Y⇒Z ∘ X⇒Y ] , μZ) , v

    combine-cong : ∀ P {Y}{v v' : Carrier (∃Result Y (F₀ (omap P)))} →
                    (v≡v' : Setoid._≈_ (∃Result Y (F₀ (omap P))) v v') →
                    {w : Carrier (∃Result (proj₁ v) (F₀ P))} →
                    {w' : Carrier (∃Result (proj₁ v') (F₀ P))} →
                    (λ u → ∃Result u (F₀ P)) [ w ≅ w' ] →
                    Setoid._≈_ (∃Result Y (F₀ P)) (combine P v w) (combine P v' w')
    combine-cong P (hrefl (PEq.refl , geq)) (hrefl (hrefl (PEq.refl , peq))) = hrefl (PEq.refl , peq)

    ηjoin : ∀ P → Pred' [ (F₀ (omap (omap P))) , (F₀ (omap P)) ]
    _⟨$⟩_ (ηjoin P) f Y X⇒Y μY =
      let
        v@(Z , (Y⇒Z , μZ) , g) = f Y X⇒Y μY
        w@(Z' , (Z⇒Z' , μZ') , p) = g Z (Category.id C) μZ in combine P v w
    cong (ηjoin P){i = i}{j} i≡j Y X⇒Y μY = combine-cong P (i≡j Y X⇒Y μY) (lem P (i≡j Y X⇒Y μY))
      where
        lem : ∀ P {X}{v v' : Carrier (∃Result X (F₀ (omap P)))} → (∃Result X (F₀ (omap P))) [ v ≈ v' ] →
              (λ u → ∃Result u (F₀ P)) [ (proj₂ (proj₂ v)) (proj₁ v) (id C) (proj₂ (proj₁ (proj₂ v))) ≅
              (proj₂ (proj₂ v')) (proj₁ v') (id C) (proj₂ (proj₁ (proj₂ v'))) ]
        lem P {X} {Σ , S , g} {.Σ , .S , g'} (hrefl  (PEq.refl , g≡g')) = hrefl (g≡g' Σ (id C) (proj₂ S))

  join : ∀ (P : Obj MP) → MP [ omap (omap P) , omap P ]
  (η (join P) X) = ηjoin P
  commute (join P) {X}{Y} X⇒Y {x}{y} x≡y =
    begin
      (ISetoids ℓ ℓ [ η (join P) Y ∘ (F₁ (omap (omap P)) X⇒Y)] ⟨$⟩ x)
        ↓⟨ _⟶_.cong (ISetoids ℓ ℓ [ η (join P) Y ∘ (F₁ (omap (omap P)) X⇒Y)]) x≡y ⟩
      (ISetoids ℓ ℓ [ η (join P) Y ∘ (F₁ (omap (omap P)) X⇒Y)] ⟨$⟩ y)
        ↓≣⟨ PEq.refl ⟩
      (ηjoin P ⟨$⟩ ((F₁ (omap (omap P)) X⇒Y) ⟨$⟩ y))
        ↓⟨ {!!} ⟩
      (F₁ (omap P) X⇒Y) ⟨$⟩ (ηjoin P ⟨$⟩ y)
        ↓≣⟨ PEq.refl ⟩
      (ISetoids ℓ ℓ [ F₁ (omap P) X⇒Y ∘ (η (join P) X) ] ⟨$⟩ y) ∎
    where open SetoidReasoning (F₀ (omap P) Y)

  .homomorphism' : ∀ {X Y Z : Obj MP}(f : MP [ X , Y ])(g : MP [ Y , Z ]) →
                   MP [ hmap (MP [ g ∘ f ]) ≡ MP [ hmap g ∘ hmap f ] ]
  homomorphism' {P}{Q}{R} F G {x = X}{f}{g} f≡g Y X⇒Y μY =
    let
      (Z , S , v) = f Y X⇒Y μY
      (U , T , w) = g Y X⇒Y μY
    in begin
      Z , S , η (MP [ G ∘ F ]) Z ⟨$⟩ v
        ≈⟨ ≅cong (result-map (F₀ P) (F₀ R) (η (MP [ G ∘ F ]) _)) (f≡g Y X⇒Y μY) ⟩
      U , T , η (MP [ G ∘ F ]) U ⟨$⟩ w ∎
    where open SetoidReasoning (∃Result Y (F₀ R))

  .resp-≡ : {P Q : Obj MP}(F G : MP [ P , Q ]) → MP [ F ≡ G ] → MP [ hmap F ≡ hmap G ]
  resp-≡ {P} {Q} F G F≡G {x} {f} {g} f≡g Y X⇒Y μY =
    let
      (Z , S , v) = f Y X⇒Y μY
      (U , T , w) = g Y X⇒Y μY
    in begin
      (Z , S , η F Z ⟨$⟩ v)
        ≈⟨ ≅cong (result-map (F₀ P) (F₀ Q) (η F _)) (f≡g Y X⇒Y μY) ⟩
      (U , T , η F U ⟨$⟩ w)
        ≈⟨ hrefl (PEq.refl , F≡G (Setoid.refl (F₀ P (proj₁ (g Y X⇒Y μY))))) ⟩
      (U , T , η G U ⟨$⟩ w) ∎
    where open SetoidReasoning (∃Result Y (F₀ Q))

open Monad
open Functor
open IndexedSetoid

St : Monad MP
F St = record {
    F₀ = State.omap
  ; F₁ = State.hmap
  ; identity = Fun.id
  ; homomorphism = λ{ {f = f}{g} → State.homomorphism' f g }
  ; F-resp-≡ = λ{ {F = F}{G} → State.resp-≡ F G }}

-- natural return
η (η St) = State.return
commute (η St) X⇒Y {Σ₀}{x}{y} x≡y Σ Σ₀⇒Σ μΣ = hrefl (PEq.refl , {!!})

-- natural join
η (μ St) = State.join
commute (μ St) X⇒Y eq Σ x⇒Σ μΣ = {!!}

-- laws
assoc St = {!!}
identityˡ St = λ x a a₁ a₂ → {!!}
identityʳ St = {!!}
