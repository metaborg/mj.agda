open import Categorical.Preorder

module Categorical.MonotonePredicates.Monads.Predicate {ℓ ℓ₂}
  (po : PreorderPlus ℓ ℓ₂ ℓ)
  -- probably should be Pred
  (Pr : PreorderPlus.Carrier po → Set ℓ) where

open import Categorical.MonotonePredicates po
open PreorderPlus po hiding (po; assoc) renaming (Carrier to Shape)

open import Level

open import Data.Product
open import Function as Fun using (case_of_;_∋_)
open import Relation.Binary.Core
open import Relation.Binary using (IsPreorder) renaming (Preorder to Po)
open import Relation.Binary.PropositionalEquality as PEq using () renaming (_≡_ to _≣_)

open import Categories.Category
open import Categories.Agda
open import Categories.Functor using (Functor; Endofunctor) renaming (id to 𝕀; _∘_ to _F∘_)
open import Categories.Monad
open import Categories.Monad.Strong
open import Categories.Support.Equivalence
open import Categories.NaturalTransformation using (NaturalTransformation; _∘₀_; _∘₁_; _∘ˡ_; _∘ʳ_)
open import Categories.Support.SetoidFunctions as SF hiding (id)
open import Categories.Support.EqReasoning

open import Categorical.Predicates Shape

open NaturalTransformation using (η; commute)
open Category
open Setoid
open Functor

private
  module MP = Category MP
  C = Category.op (Preorder po)

module Result where

  -- Morally : (X ≤ Y × Pr Y) × P Y
  -- This isn't a monotone predicate... (it is anti-monotone in X)
  Result : ∀ {s₁ s₂} → Shape → Obj (Pred s₁ s₂) → Obj (Pred _ _)
  Result X P Y = (set→setoid (C [ X , Y ] × Pr Y)) ×-setoid (P Y)

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

open import Categories.Agda using (ISetoids)

module PredicateT (M : Monad (ISetoids ℓ ℓ)) where

  module M = Monad M
  module F = Functor M.F

  open Result

  -- ∃ λ (X' : Shape) → X' ≥ X × Pr X' × P X'
  ∃Result : ∀ {s₁ s₂} → Shape → Obj (Pred s₁ s₂) → Setoid _ _
  ∃Result X P = ∃[ Shape ]-setoid (Result X P)

  -- ∃Result is an anti-monotone predicate
  -- for now we'll do with the following lemma
  result-anti : ∀ {s₁ s₂ X Y}(P : Obj (Pred s₁ s₂)) → C [ X , Y ] → ∃Result Y P ⟶ ∃Result X P
  _⟨$⟩_ (result-anti P X⇒Y) (Z , (Y⇒Z , μ) , px) = Z , (C [ Y⇒Z ∘ X⇒Y ] , μ) , px
  cong (result-anti P X⇒Y) (hrefl (PEq.refl , eq)) = hrefl (PEq.refl , eq)

  result-anti-id : ∀ {s₁ s₂ X}(P : Obj (Pred s₁ s₂)) → ISetoids _ _ [ result-anti {X = X} P (id C) ≡ id (ISetoids _ _)]
  result-anti-id P (hrefl (PEq.refl , eq)) = hrefl (PEq.cong₂ _,_ (PreorderPlus.unique po _ _) PEq.refl , eq)

  -- object mapping
  -- omap P Σ ≡morally≡ ∀ Σ' → Σ' ≥ Σ → Pr Σ' → M (∃ λ Σ'' → Σ'' ≥ Σ' × Pr Σ'' × P Σ'')
  omap : (P : MP.Obj) → MP.Obj
  omap P = ∀-closure[ PredicateFun ]
    module omap where
      module P = Functor P

      PredicateFun : Shape → Setoid ℓ ℓ
      PredicateFun X =
        ∀[ Pr X ]-setoid λ μ → F₀ M.F (∃Result X P.F₀)

  open omap

  map-∃ : ∀ {A B c} → (MP [ A , B ]) → ISetoids _ _ [ ∃Result c (F₀ A) , ∃Result c (F₀ B) ]
  _⟨$⟩_ (map-∃ A⇒B) (Σ , S , v) = Σ , S , (η A⇒B Σ) ⟨$⟩ v
  cong (map-∃ {A} {B} A⇒B) = ≅cong (result-map (F₀ A) (F₀ B) (η A⇒B _))

  -- morphism mapping
  hmap : ∀ {A B : MP.Obj} → MP [ A , B ] → MP [ omap A , omap B ]
  _⟨$⟩_ (η (hmap A⇒B) X) φ    C X⇒C μ = F.F₁ (map-∃ A⇒B) ⟨$⟩ (φ C X⇒C μ)
  cong  (η (hmap A⇒B) X) φ≡φ' C X⇒C μ = F.F-resp-≡ (cong (map-∃ A⇒B)) (φ≡φ' C X⇒C μ)
  commute (hmap {A} {B} A⇒B) {X = X}{Y} X⇒Y {x} {y} x≡y =
    begin
      (ISetoids _ _ [ η (hmap A⇒B) Y ∘ (F₁ (omap A) X⇒Y) ] ⟨$⟩ x)
    ↓⟨ cong ((ISetoids ℓ ℓ ∘ η (hmap A⇒B) Y) (F₁ (omap A) X⇒Y)) x≡y ⟩
      (ISetoids _ _ [ η (hmap A⇒B) Y ∘ (F₁ (omap A) X⇒Y) ] ⟨$⟩ y)
    ↓⟨ Setoid.refl (F₀ (omap B) Y) ⟩
      (ISetoids _ _ [ F₁ (omap B) X⇒Y ∘ (η (hmap A⇒B) X) ] ⟨$⟩ y) ∎
    where open SetoidReasoning (F₀ (omap B) Y)

  .homomorphism' : ∀ {X Y Z : Obj MP}(f : MP [ X , Y ])(g : MP [ Y , Z ]) →
                   MP [ hmap (MP [ g ∘ f ]) ≡ MP [ hmap g ∘ hmap f ] ]
  homomorphism' {P}{Q}{R} F G {x = X}{f}{g} f≡g C X⇒C μ =
    begin
      F.F₁ (map-∃ (MP [ G ∘ F ])) ⟨$⟩ f C X⇒C μ
    ↓⟨ F.homomorphism (f≡g C X⇒C μ) ⟩
      F.F₁ (map-∃ G) ⟨$⟩ (F.F₁ (map-∃ F) ⟨$⟩ g C X⇒C μ)
    ↓≣⟨ PEq.refl ⟩
      ((η (MP [ hmap G ∘ hmap F ]) X ⟨$⟩ g)) C X⇒C μ ∎
    where open SetoidReasoning (F.F₀ (∃Result C (F₀ R)))

  .resp-≡ : {P Q : Obj MP}(F G : MP [ P , Q ]) → MP [ F ≡ G ] → MP [ hmap F ≡ hmap G ]
  resp-≡ {P} {Q} F G F≡G {x} {f} {g} f≡g Y X⇒Y μY =
    begin
      F.F₁ (map-∃ F) ⟨$⟩ f Y X⇒Y μY
    ↓⟨ cong (F.F₁ (map-∃ F)) (f≡g Y X⇒Y μY) ⟩
      F.F₁ (map-∃ F) ⟨$⟩ g Y X⇒Y μY
    ↓⟨ F.F-resp-≡ (λ{ (hrefl (PEq.refl , eq)) → hrefl (PEq.refl , F≡G eq)}) (Setoid.refl (F.F₀ (∃Result Y (F₀ P)))) ⟩
      F.F₁ (map-∃ G) ⟨$⟩ g Y X⇒Y μY ∎
    where open SetoidReasoning (F.F₀ (∃Result Y (F₀ Q)))

  .identity′ : ∀ {P} → MP [ hmap {P} MP.id ≡ MP.id ]
  identity′ {P} {x}{f}{g} f≡g C X⇒C μ = F.identity (f≡g C X⇒C μ)

  functor : Endofunctor MP
  functor = record
    {F₀ = omap
    ; F₁ = hmap
    ; identity = λ {P} → identity′ {P}
    ; homomorphism = λ{ {f = f}{g} → homomorphism' f g }
    ; F-resp-≡ = λ{ {F = F}{G} → resp-≡ F G }}

  return : ∀ (P : Obj MP) → MP [ P , omap P ]
  _⟨$⟩_ (η (return P) X) x Y X⇒Y μ = η M.η _ ⟨$⟩ (Y , (id C , μ) , (F₁ P X⇒Y) ⟨$⟩ x)
  cong (η (return P) X) i≡j Y X⇒Y μ = cong (η M.η _) (hrefl (PEq.refl , cong (F₁ P X⇒Y) i≡j ))
  commute (return P) {X}{Y} X⇒Y {x}{y} x≡y Z Y⇒Z μZ =
    begin
      (ISetoids ℓ ℓ [ η (return P) Y ∘ (F₁ P X⇒Y) ] ⟨$⟩ x) Z Y⇒Z μZ
    ↓≣⟨ PEq.refl ⟩
      η M.η _ ⟨$⟩ (Z , (id C , μZ) , F₁ P Y⇒Z ⟨$⟩ (F₁ P X⇒Y ⟨$⟩ x))
    ↑⟨ cong (η M.η _) (hrefl (PEq.refl , homomorphism P (Setoid.sym (F₀ P X) x≡y))) ⟩
      η M.η _ ⟨$⟩ (Z , (id C , μZ) , F₁ P (C [ Y⇒Z ∘ X⇒Y ]) ⟨$⟩ y)
    ↓≣⟨ PEq.refl ⟩
      (ISetoids ℓ ℓ [ F₁ (omap P) X⇒Y ∘ (η (return P) X) ] ⟨$⟩ y) Z Y⇒Z μZ ∎
    where open SetoidReasoning (F.F₀ (∃Result Z (F₀ P)))

  private
    collapse : ∀ P {Y} → ISetoids ℓ ℓ [ ∃Result Y (F₀ (omap P)) , F.F₀ (∃Result Y (F₀ P)) ]
    _⟨$⟩_ (collapse P) (Y , (X⇒Y , μ) , f) =
      F.F₁ (result-anti (F₀ P) X⇒Y) ⟨$⟩ (f Y (id C) μ)
    cong  (collapse P) {Σ , (X⇒Y , μ) , v} {._ , ._ , v'} (hrefl (PEq.refl , eq)) =
      F.F-resp-≡ (cong (result-anti (F₀ P) X⇒Y)) (eq Σ (id C) μ)

    .collapse-return : ∀ {P} Y → ISetoids _ _ [ (ISetoids _ _ [ collapse P {Y} ∘ (map-∃ (return P)) ]) ≡ η M.η _ ]
    collapse-return {P} Y {(Σ , (X⇒Y , μ) , v)}{y} x≡y =
      begin
        F.F₁ (result-anti (F₀ P) X⇒Y) ⟨$⟩ (η M.η _ ⟨$⟩ (Σ , (id C , μ) , (F₁ P (id C)) ⟨$⟩ v))
      ↑⟨ commute M.η (result-anti (F₀ P) X⇒Y) (Setoid.refl (∃Result Σ (F₀ P))) ⟩
        η M.η _ ⟨$⟩ ((result-anti (F₀ P) X⇒Y) ⟨$⟩ (Σ , (id C , μ) , (F₁ P (id C)) ⟨$⟩ v))
      ↓⟨ cong (η M.η _) (hrefl (PEq.cong₂ _,_ (Category.identityˡ C) PEq.refl , identity P (Setoid.refl (F₀ P Σ)))) ⟩
        η M.η _ ⟨$⟩ (Σ , (X⇒Y , μ) , v)
      ↓⟨ cong (η M.η _) x≡y ⟩
        η M.η _ ⟨$⟩ y
      ∎
      where open SetoidReasoning (F.F₀ (∃Result Y (F₀ P)))

    .anti-map-∃-comm : ∀ {P Q : Obj MP}{X Y} (X⇒Y : C [ X , Y ]) (P⇒Q : MP [ P , Q ]) →
                       ISetoids _ _ [ (ISetoids _ _ [ result-anti (F₀ Q) X⇒Y ∘ (map-∃ P⇒Q) ]) ≡
                                      (ISetoids _ _ [ map-∃ P⇒Q ∘ (result-anti (F₀ P) X⇒Y) ]) ]
    anti-map-∃-comm {P}{Q}{X}{Y} X⇒Y P⇒Q {(Z , (Y⇒Z , μ), v)}{y} x≡y =
      cong (map-∃ P⇒Q) (cong (result-anti (F₀ P) X⇒Y) x≡y)

    .collapse-lem : ∀ {P Q}(P⇒Q : MP [ P , Q ]) Y →
                    ISetoids _ _ [
                      ISetoids ℓ ℓ [ collapse Q {Y} ∘ map-∃ (hmap P⇒Q) ] ≡
                      ISetoids ℓ ℓ [ F.F₁ (map-∃ P⇒Q) ∘ collapse P ]
                    ]
    collapse-lem {P} {Q} P⇒Q Y {x} {(X , (X⇒Y , μ) , f)} x≡y =
      begin
        collapse Q ⟨$⟩ (map-∃ (hmap P⇒Q) ⟨$⟩ x)
      ↓⟨ cong (collapse Q) (cong (map-∃ (hmap P⇒Q)) x≡y) ⟩
        collapse Q ⟨$⟩ (map-∃ (hmap P⇒Q) ⟨$⟩ (X , (X⇒Y , μ) , f))
      ↓≣⟨ PEq.refl ⟩
        F.F₁ (result-anti (F₀ Q) X⇒Y) ⟨$⟩ ((η (hmap P⇒Q) X ⟨$⟩ f) X (id C) μ)
      ↓≣⟨ PEq.refl ⟩
        F.F₁ (result-anti (F₀ Q) X⇒Y) ⟨$⟩ (F.F₁ (map-∃ P⇒Q) ⟨$⟩ (f X (id C) μ))
      ↑⟨ F.homomorphism (Setoid.refl (F.F₀ (∃Result X (F₀ P)))) ⟩
        F.F₁ (ISetoids _ _ [ result-anti (F₀ Q) X⇒Y ∘ (map-∃ P⇒Q) ]) ⟨$⟩ (f X (id C) μ)
      ↓⟨ F.F-resp-≡ (anti-map-∃-comm X⇒Y P⇒Q) (Setoid.refl (F.F₀ (∃Result X (F₀ P)))) ⟩
        F.F₁ (ISetoids _ _ [ map-∃ P⇒Q ∘ (result-anti (F₀ P) X⇒Y) ]) ⟨$⟩ (f X (id C) μ)
      ↓⟨ F.homomorphism (Setoid.refl (F.F₀ (∃Result X (F₀ P)))) ⟩
        F.F₁ (map-∃ P⇒Q) ⟨$⟩ (F.F₁ (result-anti (F₀ P) X⇒Y) ⟨$⟩ (f X (id C) μ))
      ↓≣⟨ PEq.refl ⟩
        F.F₁ (map-∃ P⇒Q) ⟨$⟩ (collapse P ⟨$⟩ (X , (X⇒Y , μ) , f))
      ∎
      where open SetoidReasoning (F.F₀ (∃Result Y (F₀ Q)))

    ηjoin : ∀ P → Pred' [ (F₀ (omap (omap P))) , (F₀ (omap P)) ]
    _⟨$⟩_ (ηjoin P) f Y X⇒Y μY =
      ISetoids _ _ [ η M.μ _ ∘ (F.F₁ (collapse P)) ] ⟨$⟩ (f Y X⇒Y μY)
    cong (ηjoin P){i = i}{j} i≡j Y X⇒Y μY =
      cong (η M.μ _) (cong (F.F₁ (collapse P)) (i≡j Y X⇒Y μY))

  join : ∀ (P : Obj MP) → MP [ omap (omap P) , omap P ]
  (η (join P) X) = ηjoin P
  commute (join P) {X}{Y} X⇒Y {x}{y} x≡y =
    begin
      (ISetoids ℓ ℓ [ η (join P) Y ∘ (F₁ (omap (omap P)) X⇒Y)] ⟨$⟩ x)
    ↓⟨ _⟶_.cong (ISetoids ℓ ℓ [ η (join P) Y ∘ (F₁ (omap (omap P)) X⇒Y)]) x≡y ⟩
      (ISetoids ℓ ℓ [ η (join P) Y ∘ (F₁ (omap (omap P)) X⇒Y)] ⟨$⟩ y)
    ↓≣⟨ PEq.refl ⟩
      (ISetoids ℓ ℓ [ F₁ (omap P) X⇒Y ∘ (η (join P) X) ] ⟨$⟩ y)
    ∎
    where open SetoidReasoning (F₀ (omap P) Y)

  open Monad
  open Functor

  monad : Monad MP
  F monad = functor

  -- natural return
  η (η monad) = return
  commute (η monad) {P}{Q} P⇒Q {X}{x}{y} x≡y =
    begin
      (η (MP [ (return Q) ∘ P⇒Q ]) X ⟨$⟩ x)
    ↓⟨ cong (η (MP [ return Q ∘ P⇒Q ]) X) x≡y ⟩
      (η (return Q) X) ⟨$⟩ (η P⇒Q X ⟨$⟩ y)
    ↓≣⟨ PEq.refl ⟩
      (λ Y X⇒Y μ → η M.η _ ⟨$⟩ (Y , (id C , μ) , (F₁ Q X⇒Y) ⟨$⟩ (η P⇒Q X ⟨$⟩ y)))
    ↑⟨ (λ Y F μ → cong (η M.η _) (hrefl (PEq.refl , commute P⇒Q F (Setoid.refl (F₀ P X))))) ⟩
      (λ Y X⇒Y μ → η M.η _ ⟨$⟩ (Y , (id C , μ) , η P⇒Q Y ⟨$⟩ ((F₁ P X⇒Y) ⟨$⟩ y)))
    ↓≣⟨ PEq.refl ⟩
      (λ Y X⇒Y μ → η M.η _ ⟨$⟩ ((map-∃ P⇒Q) ⟨$⟩ (Y , (id C , μ) , (F₁ P X⇒Y) ⟨$⟩ y)))
    ↓⟨ (λ Y X⇒Y μ → commute M.η (map-∃ P⇒Q) (hrefl (PEq.refl , (Setoid.refl (F₀ P Y))))) ⟩
      (η (hmap P⇒Q) X) ⟨$⟩ (λ Y X⇒Y μ → (η M.η _ ⟨$⟩ (Y , (id C , μ) , (F₁ P X⇒Y) ⟨$⟩ y)))
    ↓≣⟨ PEq.refl ⟩
      (η (hmap P⇒Q) X) ⟨$⟩ (η (return P) X ⟨$⟩ y)
    ∎
    where
      open SetoidReasoning (F₀ (omap Q) X)

  -- natural join
  η (μ monad) = join
  commute (μ monad) {P} {Q} P⇒Q {X} {x} {y} x≡y Y X⇒Y μY =
    begin
      (η (join Q MP.∘ (hmap (hmap P⇒Q))) X ⟨$⟩ x) Y X⇒Y μY
    ↓⟨ (cong (η (join Q MP.∘ (hmap (hmap P⇒Q))) X) x≡y) Y X⇒Y μY ⟩
      (η (join Q MP.∘ (hmap (hmap P⇒Q))) X ⟨$⟩ y) Y X⇒Y μY
    ↓≣⟨ PEq.refl ⟩
      (ISetoids _ _ [ η M.μ _ ∘ F.F₁ (collapse Q) ]) ⟨$⟩ ((η (hmap (hmap P⇒Q)) X ⟨$⟩ y) Y X⇒Y μY)
    ↓≣⟨ PEq.refl ⟩
      (η M.μ _ ⟨$⟩ ((F.F₁ (collapse Q)) ⟨$⟩ (F.F₁ (map-∃ (hmap P⇒Q)) ⟨$⟩ (y Y X⇒Y μY))))
    ↑⟨ cong (η M.μ _) (F.homomorphism (Setoid.refl (F.F₀ (∃Result Y (F₀ (omap P)))))) ⟩
      η M.μ _ ⟨$⟩ (F.F₁ (ISetoids _ _ [ collapse Q  ∘ (map-∃ (hmap P⇒Q)) ]) ⟨$⟩ (y Y X⇒Y μY))
    ↓⟨ cong (η M.μ _) (F.F-resp-≡ (collapse-lem P⇒Q Y) (Setoid.refl (F.F₀ (∃Result Y (F₀ (omap P)))))) ⟩
      η M.μ _ ⟨$⟩ (F.F₁ (ISetoids _ _ [ F.F₁ (map-∃ P⇒Q) ∘ collapse P ]) ⟨$⟩ (y Y X⇒Y μY))
    ↓⟨ cong (η M.μ _) (F.homomorphism (Setoid.refl (F.F₀ (∃Result Y (F₀ (omap P)))))) ⟩
      η M.μ _ ⟨$⟩ (F.F₁ (F.F₁ (map-∃ P⇒Q)) ⟨$⟩ (F.F₁ (collapse P) ⟨$⟩ y Y X⇒Y μY))
    ↓⟨ commute M.μ (map-∃ P⇒Q) (Setoid.refl (F₀ (M.F F∘ M.F) (∃Result Y (F₀ P)))) ⟩
      F.F₁ (map-∃ P⇒Q) ⟨$⟩ (η M.μ _ ⟨$⟩ (F.F₁ (collapse P) ⟨$⟩ y Y X⇒Y μY))
    ↓≣⟨ PEq.refl ⟩
      F.F₁ (map-∃ P⇒Q) ⟨$⟩ ((ISetoids _ _ [ η M.μ _ ∘ F.F₁ (collapse P) ]) ⟨$⟩ y Y X⇒Y μY)
    ↓≣⟨ PEq.refl ⟩
      (η (hmap P⇒Q MP.∘ join P) X ⟨$⟩ y) Y X⇒Y μY
    ∎
    where
      open SetoidReasoning (F.F₀ (∃Result Y (F₀ Q)))

  assoc monad {P}{Σ}{x = x}{y} x≡y Y Σ⇒Y μY =
    begin
      ((η (η (μ monad) P) Σ) ⟨$⟩ ((η (F₁ functor (η (μ monad) P)) Σ) ⟨$⟩ x)) Y Σ⇒Y μY
    ↓⟨ cong (η (η (μ monad ∘₁ functor ∘ˡ μ monad) P) Σ) x≡y Y Σ⇒Y μY ⟩
      ((η (η (μ monad) P) Σ) ⟨$⟩ ((η (F₁ functor (η (μ monad) P)) Σ) ⟨$⟩ y)) Y Σ⇒Y μY
    ↓⟨ {!!} ⟩ -- hrefl (PEq.cong₂ _,_ (PreorderPlus.unique po _ _) PEq.refl , Setoid.refl (F₀ P _)) ⟩
      ((η (η (μ monad) P) Σ) ⟨$⟩ (η (η (μ monad) (F₀ functor P)) Σ ⟨$⟩ y)) Y Σ⇒Y μY
    ∎
    where open SetoidReasoning (F.F₀ (∃Result Y (F₀ P)))

  identityˡ monad {P}{Σ} {x}{y} x≡y Y X⇒Y μY =
    begin
      (η M.μ (∃Result Y (F₀ P))) ⟨$⟩ (F.F₁ (collapse P) ⟨$⟩ (F.F₁ (map-∃ (return P)) ⟨$⟩ x Y X⇒Y μY))
    ↑⟨ (cong (η M.μ (∃Result Y (F₀ P))) (F.homomorphism (Setoid.refl (F.F₀ (∃Result Y (F₀ P)))))) ⟩
      (η M.μ (∃Result Y (F₀ P))) ⟨$⟩ (F.F₁ (ISetoids _ _ [ collapse P ∘ (map-∃ (return P)) ]) ⟨$⟩ x Y X⇒Y μY)
    ↓⟨ cong (η M.μ (∃Result Y (F₀ P))) (F.F-resp-≡ (collapse-return {P} Y) (Setoid.refl (F.F₀ (∃Result Y (F₀ P))))) ⟩
      (η M.μ (∃Result Y (F₀ P))) ⟨$⟩ (F.F₁ (η M.η _) ⟨$⟩ x Y X⇒Y μY)
    ↓⟨ M.identityˡ (x≡y Y X⇒Y μY) ⟩
      y Y X⇒Y μY
    ∎
    where open SetoidReasoning (F.F₀ (∃Result Y (F₀ P)))

  identityʳ monad {P}{Σ} {x}{y} x≡y Y X⇒Y μY =
    begin
       (η M.μ _ ⟨$⟩ ((F.F₁ (collapse P)) ⟨$⟩ ((η (return (F₀ functor P)) Σ ⟨$⟩ x) Y X⇒Y μY)))
    ↓≣⟨ PEq.refl ⟩
       (η M.μ _ ⟨$⟩ ((F.F₁ (collapse P)) ⟨$⟩ (η M.η _ ⟨$⟩ (Y , (id C , μY) , (F₁ (F₀ functor P) X⇒Y) ⟨$⟩ x))))
    ↑⟨ cong (η M.μ _) (commute M.η (collapse P) (Setoid.refl (∃Result Y (F₀ (omap P))))) ⟩
       (η M.μ _ ⟨$⟩ (η M.η _ ⟨$⟩ (collapse P ⟨$⟩ (Y , (id C , μY) , (F₁ (F₀ functor P) X⇒Y) ⟨$⟩ x))))
    ↓≣⟨ PEq.refl ⟩
       (η M.μ _ ⟨$⟩ (η M.η _ ⟨$⟩ (F.F₁ (result-anti (F₀ P) (id C)) ⟨$⟩ (((F₁ (F₀ functor P) X⇒Y) ⟨$⟩ x) Y (id C) μY))))
    ↓⟨ cong (η M.μ _) (cong (η M.η _) (F.F-resp-≡ (result-anti-id (F₀ P)) (Setoid.refl (F.F₀ (∃Result Y (F₀ P)))))) ⟩
       (η M.μ _ ⟨$⟩ (η M.η _ ⟨$⟩ (F.F₁ (id (ISetoids _ _)) ⟨$⟩ (((F₁ (F₀ functor P) X⇒Y) ⟨$⟩ x) Y (id C) μY))))
    ↓⟨ cong (η M.μ _) (cong (η M.η _) (F.identity (Setoid.refl (F.F₀ (∃Result Y (F₀ P)))))) ⟩
       (η M.μ _ ⟨$⟩ (η M.η _ ⟨$⟩ (x Y (C [ id C ∘ X⇒Y ]) μY)))
    ↓⟨ cong (η M.μ _) (cong (η M.η _) ((Setoid.reflexive (F.F₀ (∃Result Y (F₀ P))) (PEq.cong (λ u → x Y u μY) (PreorderPlus.unique  po _ _))))) ⟩
       (η M.μ _ ⟨$⟩ (η M.η _ ⟨$⟩ x Y X⇒Y μY))
    ↓⟨ M.identityʳ (x≡y Y X⇒Y μY) ⟩
      y Y X⇒Y μY
    ∎
    where open SetoidReasoning (F.F₀ (∃Result Y (F₀ P)))

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

open import Categorical.ISetoids.Monads.Identity
Predicate :  Monad MP
Predicate = PredicateT.monad idM
