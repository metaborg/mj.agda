open import Categorical.Preorder

module Categorical.MonotonePredicates.Monads.Predicate {ℓ ℓ₂}
  (po : PreorderPlus ℓ ℓ₂ ℓ)
  (Store : PreorderPlus.Carrier po → Set ℓ) where

open import Categorical.MonotonePredicates po
open PreorderPlus po hiding (po; assoc) renaming (Carrier to Shape)

open import Level

open import Data.Product
open import Function as Fun using (case_of_;_∋_)
open import Relation.Binary.Core
open import Relation.Binary using (IsPreorder) renaming (Preorder to Po)
open import Relation.Binary.PropositionalEquality as PEq using () renaming (_≡_ to _≣_)
open import Relation.Binary.HeterogeneousEquality as HEq using () renaming (_≅_ to _≡~_)

open import Categories.Category
open import Categories.Agda
open import Categories.Functor using (Functor; Endofunctor) renaming (id to 𝕀; _∘_ to _F∘_)
open import Categories.Monad
open import Categories.Monad.Strong
open import Categories.Support.Equivalence
open import Categories.NaturalTransformation using (NaturalTransformation; _∘₁_; _∘ˡ_; _∘ʳ_)
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

  -- Morally : (X ≤ Y × Predicate Y) × P Y
  -- This isn't a monotone predicate... (it is anti-monotone in X)
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

open import Categories.Agda using (ISetoids)

module PredicateT (M : Monad (ISetoids ℓ ℓ)) where

  module M = Monad M
  module F = Functor M.F

  open Result

  ∃Result : ∀ {s₁ s₂} → Shape → Obj (Pred s₁ s₂) → Setoid _ _
  ∃Result Σ P = ∃[ Shape ]-setoid (Result Σ P)

  -- ∃Result is an anti-monotone predicate
  -- for now we'll do with the following lemma
  result-anti : ∀ {s₁ s₂ X Y}(P : Obj (Pred s₁ s₂)) → C [ X , Y ] → ∃Result Y P ⟶ ∃Result X P
  _⟨$⟩_ (result-anti P X⇒Y) (Z , (Y⇒Z , μ) , px) = Z , (C [ Y⇒Z ∘ X⇒Y ] , μ) , px
  cong (result-anti P X⇒Y) (hrefl (PEq.refl , eq)) = hrefl (PEq.refl , eq)

  -- object mapping
  omap : (P : MP.Obj) → MP.Obj
  omap P = ∀-closure[ PredicateFun ]
    module omap where
      module P = Functor P

      PredicateFun : Shape → Setoid ℓ ℓ
      PredicateFun X =
        ∀[ Store X ]-setoid λ μ → F₀ M.F (∃Result X P.F₀)

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
      (ISetoids ℓ ℓ [ F₁ (omap P) X⇒Y ∘ (η (join P) X) ] ⟨$⟩ y) ∎
    where open SetoidReasoning (F₀ (omap P) Y)

  open Monad
  open Functor

  monad : Monad MP
  F monad = functor

  -- natural return
  η (η monad) = return
  commute (η monad) {P}{Q} P⇒Q {X}{x}{y} x≡y =
    begin
        (η (MP [ (return Q) ∘ (F₁ (𝕀 {C = MP}) P⇒Q) ]) X ⟨$⟩ x)
      ↓⟨ cong (η (MP [ return Q ∘ F₁ (𝕀 {C = MP}) P⇒Q ]) X) x≡y ⟩
        (η (return Q) X) ⟨$⟩ (η (F₁ (𝕀 {C = MP}) P⇒Q) X ⟨$⟩ y)
      ↓≣⟨ PEq.refl ⟩
        (λ Y X⇒Y μ → η M.η _ ⟨$⟩ (Y , (id C , μ) , (F₁ Q X⇒Y) ⟨$⟩ (η P⇒Q X ⟨$⟩ y)))
      ↑⟨ (λ Y F μ → cong (η M.η _) (hrefl (PEq.refl , commute P⇒Q F (Setoid.refl (F₀ P X))))) ⟩
        (λ Y X⇒Y μ → η M.η _ ⟨$⟩ (Y , (id C , μ) , η P⇒Q Y ⟨$⟩ ((F₁ P X⇒Y) ⟨$⟩ y)))
      ↓≣⟨ PEq.refl ⟩
        (λ Y X⇒Y μ → η M.η _ ⟨$⟩ ((F₁ (𝕀 {C = ISetoids _ _}) (map-∃ P⇒Q)) ⟨$⟩ (Y , (id C , μ) , (F₁ P X⇒Y) ⟨$⟩ y)))
      ↓⟨ (λ Y X⇒Y μ → commute M.η (map-∃ P⇒Q) (hrefl (PEq.refl , (Setoid.refl (F₀ P Y))))) ⟩
        (η (hmap P⇒Q) X) ⟨$⟩ (λ Y X⇒Y μ → (η M.η _ ⟨$⟩ (Y , (id C , μ) , (F₁ P X⇒Y) ⟨$⟩ y)))
      ↓≣⟨ PEq.refl ⟩
        (η (hmap P⇒Q) X) ⟨$⟩ (η (return P) X ⟨$⟩ y) ∎
    where
      open SetoidReasoning (F₀ (omap Q) X)

  -- natural join
  η (μ monad) = join
  commute (μ monad) {P} {Q} P⇒Q {X} {x} {y} x≡y =
    begin
        η (join Q MP.∘ (hmap (hmap P⇒Q))) X ⟨$⟩ x
      ↓⟨ cong (η (join Q MP.∘ (hmap (hmap P⇒Q))) X) x≡y ⟩
        η (join Q MP.∘ (hmap (hmap P⇒Q))) X ⟨$⟩ y
      ↓≣⟨ PEq.refl ⟩
        (λ Y X⇒Y μ → (ISetoids _ _ [ η M.μ _ ∘ F.F₁ (collapse Q) ]) ⟨$⟩ ((η (hmap (hmap P⇒Q)) X ⟨$⟩ y) Y X⇒Y μ))
      ↓⟨ (λ Y X⇒Y μ → {!!}) ⟩ -- PEq.refl ⟩
        (λ Y X⇒Y μ → F.F₁ (map-∃ P⇒Q) ⟨$⟩ ((ISetoids _ _ [ η M.μ _ ∘ F.F₁ (collapse P) ]) ⟨$⟩ y Y X⇒Y μ))
      ↓≣⟨ PEq.refl ⟩
        η (hmap P⇒Q) X ⟨$⟩ (λ Y X⇒Y μ → (ISetoids _ _ [ η M.μ _ ∘ F.F₁ (collapse P) ]) ⟨$⟩ y Y X⇒Y μ)
      ↓≣⟨ PEq.refl ⟩
        η (hmap P⇒Q MP.∘ join P) X ⟨$⟩ y
      ∎
    where
      open SetoidReasoning (F₀ (omap Q) X)

  assoc monad {P}{Σ}{x = x}{y} x≡y Y Σ⇒Y μY =
    begin
      ((η (η (μ monad) P) Σ) ⟨$⟩ ((η (F₁ functor (η (μ monad) P)) Σ) ⟨$⟩ x)) Y Σ⇒Y μY
        ↓⟨ cong (η (η (μ monad ∘₁ functor ∘ˡ μ monad) P) Σ) x≡y Y Σ⇒Y μY ⟩
      ((η (η (μ monad) P) Σ) ⟨$⟩ ((η (F₁ functor (η (μ monad) P)) Σ) ⟨$⟩ y)) Y Σ⇒Y μY
        ↓⟨ {!!} ⟩ -- hrefl (PEq.cong₂ _,_ (PreorderPlus.unique po _ _) PEq.refl , Setoid.refl (F₀ P _)) ⟩
      ((η (η (μ monad) P) Σ) ⟨$⟩ (η (η (μ monad) (F₀ functor P)) Σ ⟨$⟩ y)) Y Σ⇒Y μY ∎
    where open SetoidReasoning (F.F₀ (∃Result Y (F₀ P)))

  identityˡ monad {P}{Σ} {x}{y} x≡y =
    begin
      -- η (η (μ monad ∘₁ functor ∘ˡ η monad) P) Σ ⟨$⟩ x
      (η (join P) Σ) ⟨$⟩ ((η (hmap (return P)) Σ) ⟨$⟩ x)
    ↓⟨ cong (η (join P) Σ) (cong (η (hmap (return P)) Σ) x≡y) ⟩
      (η (join P) Σ) ⟨$⟩ ((η (hmap (return P)) Σ) ⟨$⟩ y)
    ↓≣⟨ PEq.refl ⟩
      (λ Y X⇒Y μY → (η M.μ (∃Result Y (F₀ P))) ⟨$⟩ (F.F₁ (collapse P) ⟨$⟩ (F.F₁ (map-∃ (return P)) ⟨$⟩ y Y X⇒Y μY)))
    ↑⟨ (λ Y X⇒Y μY → cong (η M.μ (∃Result Y (F₀ P))) (F.homomorphism (Setoid.refl (F.F₀ (∃Result Y (F₀ P)))))) ⟩
      (λ Y X⇒Y μY → (η M.μ (∃Result Y (F₀ P))) ⟨$⟩
        (F.F₁ (ISetoids _ _ [ collapse P ∘ (map-∃ (return P)) ]) ⟨$⟩ y Y X⇒Y μY))
    ↓⟨ (λ Y X⇒Y μY → cong (η M.μ (∃Result Y (F₀ P))) (F.F-resp-≡ (collapse-return {P} Y) (Setoid.refl (F.F₀ (∃Result Y (F₀ P)))))) ⟩
      (λ Y X⇒Y μY → (η M.μ (∃Result Y (F₀ P))) ⟨$⟩ (F.F₁ (η M.η _) ⟨$⟩ y Y X⇒Y μY))
    ↓⟨ (λ Y X⇒Y μY → M.identityˡ (Setoid.refl (F₀ M.F (∃Result Y (F₀ P))))) ⟩
      y
    ∎
    where open SetoidReasoning (F₀ (F₀ functor P) Σ)

  identityʳ monad {P}{Σ} {x}{y} x≡y = {!!}
    where open SetoidReasoning (F₀ (omap P) Σ)

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

open import Categorical.ISetoids.Monads.Identity
Predicate :  Monad MP
Predicate = PredicateT.monad idM
