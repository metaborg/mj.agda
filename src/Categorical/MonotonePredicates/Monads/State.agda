open import Categorical.Preorder

module Categorical.MonotonePredicates.Monads.State {ℓ}
  (po : PreorderPlus ℓ ℓ ℓ)
  (Store : PreorderPlus.Carrier po → Set ℓ) where

open import Categorical.MonotonePredicates po
open PreorderPlus po hiding (po)

open import Level

open import Data.Product
open import Function using (case_of_;_∋_)
open import Relation.Binary.PropositionalEquality as PEq using () renaming (_≡_ to _≣_)
open import Relation.Binary.HeterogeneousEquality as HEq using () renaming (_≅_ to _≡~_)

open import Categories.Category
open import Categories.Agda
open import Categories.Functor hiding (_≡_; assoc; identityˡ; identityʳ; _∘_)
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.Monad
open import Categories.Monad.Strong
open import Categories.Support.Equivalence
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Support.SetoidFunctions
open import Categories.Support.EqReasoning

open NaturalTransformation using (η; commute)
open Category

private
  module MP = Category MP

-- lift equality from a set-indexed setoid into a heterogeneous equality type
-- looks like https://coq.inria.fr/distrib/current/stdlib/Coq.Logic.EqdepFacts.html -- Robbert
data _[_∼_]' {a s₁ s₂}{A : Set a}(I : A → Setoid s₁ s₂){c} :
  ∀ {c'} → Setoid.Carrier (I c) → Setoid.Carrier (I c') → Set (a ⊔ s₁ ⊔ s₂) where
  hrefl : ∀ {l r} → Setoid._≈_ (I c) l r → I [ l ∼ r ]'

.cong-∃ : ∀
          {a s₁ s₂}{A : Set a}{I : A → Setoid s₁ s₂}{J : A → Setoid s₁ s₂}
          {l l'}{r : Setoid.Carrier (I l)}{r' : Setoid.Carrier (I l')} →
          (f : ∀ {l} → (I l) ⟶ (J l)) → I [ r ∼ r' ]' → J [ (f ⟨$⟩ r) ∼ (f ⟨$⟩ r') ]'
cong-∃ f (hrefl x) = (hrefl (cong f x))

.cong-∃₂ : ∀
          {a s₁ s₂}{A : Set a}{I J K : A → Setoid s₁ s₂}{l l'}
          {i : Setoid.Carrier (I l)}{i' : Setoid.Carrier (I l')}
          {j : Setoid.Carrier (J l)}{j' : Setoid.Carrier (J l')} →
          (f : ∀ {l} → (I l) ×-setoid (J l) ⟶ (K l)) →
          I [ i ∼ i' ]' → J [ j ∼ j' ]' → K [ (f ⟨$⟩ (i , j)) ∼ (f ⟨$⟩ (i' , j')) ]'
cong-∃₂ f (hrefl x) (hrefl y) = hrefl (cong f (x , y))

∃[_]-setoid_ : ∀ {ℓ s₁ s₂} → (A : Set ℓ) → (A → Setoid s₁ s₂) → Setoid _ _
∃[ A ]-setoid B = record
   { Carrier = ∃ λ a → B.Carrier a
   ; _≈_ = λ p q → B [ (proj₂ p) ∼ (proj₂ q) ]'
   ; isEquivalence = record {
     refl = λ {x} → hrefl (Setoid.refl (B (proj₁ x))) ;
     sym = λ{ {i}{j}(hrefl p) → hrefl (Setoid.sym (B (proj₁ j)) p) };
     trans = λ{ (hrefl p) (hrefl q) → hrefl (Setoid.trans (B _) p q) }}
   }
  where
    module B a = Setoid (B a)

module IndexedSetoid where
  -- We define a category of carrier-indexed setoids.

module State where

  C = op (Preorder po)

  -- Morally : (X ≤ Y × State Y) × P Y
  -- This isn't a monotone predicate... (I think it's anti-monotone in X) -- Arjen
  Result : ∀ {s₁ s₂} → Carrier → (P : Carrier → Setoid s₁ s₂) → Carrier → Setoid _ _
  Result X P Y = (set→setoid (C [ X , Y ] × Store Y)) ×-setoid (P Y)

  -- But it should be an endofunctor of carrier indexed setoids.
  -- It suffices for now that we can map over the result with a ≈-preserving function.
  result-map : ∀ {s₁ s₂}{X Y : Carrier}(P : Carrier → Setoid s₁ s₂)(Q : Carrier → Setoid s₁ s₂) →
               (f : ∀ Y → (P Y) ⟶ (Q Y)) → Result X P Y ⟶ Result X Q Y
  result-map {X}{Y} P Q f = record
    { _⟨$⟩_ = λ x → proj₁ x , (f _) ⟨$⟩ (proj₂ x)
    ; cong  = λ x → proj₁ x , cong (f _) (proj₂ x) }

  omap : (P : MP.Obj) → MP.Obj
  omap P = ∀[ StateFun ]
    module omap where
      module P = Functor P

      -- fmap-result : ∀ {X} → (MP [ A ⇒ B ])
      StateFun : Carrier → Setoid ℓ ℓ
      StateFun X =
        ∀[ Store X ]-setoid λ μ →
        ∃[ Carrier ]-setoid (Result X P.F₀)

  open Functor
  open Category
  hmap : ∀ {A B : MP.Obj} → MP [ A , B ] → MP [ omap A , omap B ]
  _⟨$⟩_ (η (hmap A⇒B) X) φ C X⇒C μ =
    let v = φ _ X⇒C μ ; C' = proj₁ v in C' , proj₁ (proj₂ v) , (η A⇒B C') ⟨$⟩ (proj₂ (proj₂ v))
  cong (η (hmap {A}{B} A⇒B) X) φ≡φ' C X⇒C μ =
    cong-∃ (result-map (F₀ A) (F₀ B) (η A⇒B)) (φ≡φ' C X⇒C μ)
  commute (hmap {A} {B} A⇒B) X⇒Y {x} {y} x≡y Z Y⇒Z μZ =
    let X⇒Z = C [ Y⇒Z ∘ X⇒Y ] ; v = x _ X⇒Z μZ; w = y _ X⇒Z μZ in
    begin
      proj₁ v , proj₁ (proj₂ v) , (η A⇒B _) ⟨$⟩ (proj₂ (proj₂ v))
        ≈⟨ cong-∃ (result-map (F₀ A) (F₀ B) (η A⇒B)) (x≡y Z X⇒Z μZ) ⟩
      proj₁ w , proj₁ (proj₂ w) , (η A⇒B _) ⟨$⟩ (proj₂ (proj₂ w)) ∎
    where open SetoidReasoning (∃[ Carrier ]-setoid Result Z (F₀ B))


  return : ∀ (P : Obj MP) → MP [ P , omap P ]
  η (return P) X = return'
    where
      return' = record
          { _⟨$⟩_ = λ x Y X⇒Y μ → Y , (Category.id C , μ) , (Functor.F₁ P X⇒Y) ⟨$⟩ x
          ; cong = λ i≡j Y X⇒Y μ → (hrefl (PEq.refl , cong (Functor.F₁ P X⇒Y) i≡j )) }
  commute (return P) X⇒Y x≡y Z Y⇒Z μZ = (hrefl (PEq.refl , {!!}))
    where open SetoidReasoning (F₀ P Z)

  private

    combine : ∀ P {X} →
              (v : Setoid.Carrier (∃[ Carrier ]-setoid Result X (F₀ (omap P)))) →
              Setoid.Carrier (∃[ Carrier ]-setoid Result (proj₁ v) (F₀ P)) →
              Setoid.Carrier (∃[ Carrier ]-setoid Result X (F₀ P))
    combine P (Y , (X⇒Y , μY) , f) (Z , (Y⇒Z , μZ) , v) = Z , (C [ Y⇒Z ∘ X⇒Y ] , μZ) , v

    combine-cong : ∀ P {Y}{v v' : Setoid.Carrier (∃[ Carrier ]-setoid Result Y (F₀ (omap P)))} →
                    (v≡v' : Setoid._≈_ (∃[ Carrier ]-setoid Result Y (F₀ (omap P))) v v') →
                    {w : Setoid.Carrier (∃[ Carrier ]-setoid Result (proj₁ v) (F₀ P))} →
                    {w' : Setoid.Carrier (∃[ Carrier ]-setoid Result (proj₁ v') (F₀ P))} →
                    (λ u → ∃[ Carrier ]-setoid Result u (F₀ P)) [ w ∼ w' ]' →
                    Setoid._≈_ (∃[ Carrier ]-setoid Result Y (F₀ P)) (combine P v w) (combine P v' w')
    combine-cong P (hrefl (PEq.refl , geq)) (hrefl (hrefl (PEq.refl , peq))) = hrefl (PEq.refl , peq)

    join' : ∀ P {X} → Setoid.Carrier (F₀ (omap (omap P)) X) → Setoid.Carrier (F₀ (omap P) X)
    join' P f Y X⇒Y μY =
      let
        v@(Z , (Y⇒Z , μZ) , g) = f Y X⇒Y μY
        w@(Z' , (Z⇒Z' , μZ') , p) = g Z (Category.id C) μZ
      in combine P v w

    val : ∀ {C s₁ s₂}(P : Carrier → Setoid s₁ s₂) →
          (res : Setoid.Carrier (∃[ Carrier ]-setoid Result C P)) → Setoid.Carrier (P (proj₁ res))
    val _ (_ , _ , v) = v

    val-cong : ∀ {C s₁ s₂}(P : Carrier → Setoid s₁ s₂){i j} → (i≡j : Setoid._≈_ (∃[ Carrier ]-setoid Result C P) i j) →
               P [ (val P i) ∼ (val P j) ]'
    val-cong P (hrefl (_ , eq)) = hrefl eq

  join : ∀ (P : Obj MP) → MP [ omap (omap P) , omap P ]
  _⟨$⟩_ (η (join P) X) = join' P
  cong (η (join P) X) {i = i}{j} i≡j Y X⇒Y μY =
    let
      v@(Σ , (ext , μ) , g) = i Y X⇒Y μY
      v'@(Σ' , (ext' , μ') , g') = j Y X⇒Y μY
      w = g _ (Category.id C) μ
      w' = g' _ (Category.id C) μ'
      w≡w' = (λ u → ∃[ Carrier ]-setoid Result u (F₀ P)) [ w ∼ w' ]' ∋ {!!}
    in
    begin
      join' P i Y X⇒Y μY
        ↓≣⟨ PEq.refl ⟩
      combine P v w
        ↓⟨ combine-cong P (i≡j Y X⇒Y μY) w≡w' ⟩
      combine P v' w'
        ↓≣⟨ PEq.refl ⟩
      join' P j Y X⇒Y μY ∎
    where open SetoidReasoning (∃[ Carrier ]-setoid Result Y (F₀ P))
  commute (join P) X⇒Y x≡y Z Y⇒Z μZ = {!!}

  .identity' : ∀ (P : Obj MP) → MP [ hmap {P} MP.id ≡ MP.id ]
  identity' P {x = x} {x₁} {y} x₁≡y = x₁≡y

  .homomorphism' : ∀ {X Y Z : Obj MP}(f : MP [ X , Y ])(g : MP [ Y , Z ]) →
                   MP [ hmap (MP [ g ∘ f ]) ≡ MP [ hmap g ∘ hmap f ] ]
  homomorphism' {P}{Q}{R} f g {x = X}{x₁}{y} x₁≡y Y X⇒Y μY =
    let resy = (y Y X⇒Y μY) ; res = (x₁ Y X⇒Y μY) in begin
      proj₁ res , proj₁ (proj₂ res) , η (MP [ g ∘ f ]) (proj₁ res) ⟨$⟩ proj₂ (proj₂ res)
        ≈⟨ {!!} ⟩ -- cong-∃ (result-map (F₀ P) (F₀ R) (η (MP [ g ∘ f ]))) (x₁≡y Y X⇒Y μY) ⟩
      proj₁ resy , proj₁ (proj₂ resy) , η (MP [ g ∘ f ]) (proj₁ resy) ⟨$⟩ proj₂ (proj₂ resy)
        ↓≣⟨ PEq.refl ⟩
      (η (MP [ hmap g ∘ hmap f ]) X ⟨$⟩ y) Y X⇒Y μY ∎
    where open SetoidReasoning (∃[ Carrier ]-setoid Result Y (F₀ R))

  .resp-≡ : {P Q : Obj MP}(F G : MP [ P , Q ]) → MP [ F ≡ G ] → MP [ hmap F ≡ hmap G ]
  resp-≡ {P} {Q} F G F≡G {x} {f} {g} f≡g Y X⇒Y μY =
    begin
      (proj₁ (f Y X⇒Y μY) , proj₁ (proj₂ (f Y X⇒Y μY)) , η F (proj₁ (f Y X⇒Y μY)) ⟨$⟩ proj₂ (proj₂ (f Y X⇒Y μY)))
        ≈⟨ cong-∃ (result-map (F₀ P) (F₀ Q) (η F)) (f≡g Y X⇒Y μY) ⟩
      (proj₁ (g Y X⇒Y μY) , proj₁ (proj₂ (g Y X⇒Y μY)) , η F (proj₁ (g Y X⇒Y μY)) ⟨$⟩ proj₂ (proj₂ (g Y X⇒Y μY)))
        ≈⟨ hrefl (PEq.refl , F≡G (Setoid.refl (F₀ P (proj₁ (g Y X⇒Y μY))))) ⟩
      (proj₁ (g Y X⇒Y μY) , proj₁ (proj₂ (g Y X⇒Y μY)) , η G (proj₁ (g Y X⇒Y μY)) ⟨$⟩ proj₂ (proj₂ (g Y X⇒Y μY))) ∎
    where open SetoidReasoning (∃[ Carrier ]-setoid Result Y (F₀ Q))

open Monad
open Functor

St : Monad MP
F St = record {
    F₀ = State.omap
  ; F₁ = State.hmap
  ; identity = λ {P} → State.identity' P
  ; homomorphism = λ{ {f = f}{g} → State.homomorphism' f g }
  ; F-resp-≡ = λ{ {F = F}{G} → State.resp-≡ F G }}
η St = record
  { η = State.return
  ; commute = λ f x₂ a a₁ a₂ → hrefl (PEq.refl , {!!})
  }
μ St = record
  { η = State.join
  ; commute = {!!} }
assoc St = {!!}
identityˡ St = λ x a a₁ a₂ → {!!}
identityʳ St = {!!}
