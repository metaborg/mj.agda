{-# OPTIONS --allow-unsolved-metas #-}

open import Relation.Binary hiding (_⇒_)

module Experiments.Category {ℓ₁ ℓ₂ ℓ₃} (APO : Preorder ℓ₁ ℓ₂ ℓ₃) where

open import Level
open Preorder APO renaming (_∼_ to _≤_)

open import Function as Fun using (flip)
open import Relation.Unary using (Pred)
open import Data.Product as Prod using (_,_; _×_)
import Relation.Binary.PropositionalEquality as PEq
open PEq.≡-Reasoning
open import Function.Inverse using (Inverse)
open import Algebra.FunctionProperties

record IsMP {ℓ}(P : Pred Carrier ℓ) : Set (ℓ ⊔ ℓ₁ ⊔ ℓ₃) where
  field
    monotone : ∀ {c c'} → c ≤ c' → P c → P c'

    monotone-refl  : ∀ {c} p → monotone (refl {c}) p PEq.≡ p
    monotone-trans : ∀ {c c' c''} p (c~c' : c ≤ c')(c'~c'' : c' ≤ c'') →
                     monotone (trans c~c' c'~c'') p
                     PEq.≡
                     monotone c'~c'' (monotone c~c' p)

-- monotone predicates over a fixed carrier
record MP ℓ : Set (suc ℓ ⊔ ℓ₁ ⊔ ℓ₃) where
  constructor mp
  field
    pred  : Pred Carrier ℓ
    is-mp : IsMP pred

  open IsMP is-mp public

MP₀ = MP zero

-- application
_·_ : ∀ {ℓ} → MP ℓ → Carrier → Set _
(mp P _) · c = P c

-- monotone-predicate equality
_≗_ : ∀ {ℓ₁} → MP ℓ₁ → MP ℓ₁ → Set _
P ≗ Q = ∀ {c} → P · c PEq.≡ Q · c

import Data.Unit as Unit

Const : ∀ {ℓ}(P : Set ℓ) → MP ℓ
Const P = mp (λ _ → P) (record {
    monotone = λ x p → p ;
    monotone-refl = λ p → PEq.refl ;
    monotone-trans = λ p c~c' c'~c'' → PEq.refl
  })

⊤ : MP zero
⊤ = Const Unit.⊤

-- we package the Agda function that represents morphisms
-- in this category in a record such that P ⇒ Q doesn't get
-- reduced to the simple underlying type of `apply`
infixl 30 _⇒_
record _⇒_ {p q}(P : MP p)(Q : MP q) : Set (p ⊔ q ⊔ ℓ₁ ⊔ ℓ₃) where
  constructor mk⇒

  field
    apply         : ∀ {c} → P · c → Q · c

    monotone-comm : ∀ {c c'}(c~c' : c ≤ c'){p : P · c} →
                    apply {c'} (MP.monotone P c~c' p) PEq.≡ MP.monotone Q c~c' (apply p)

open _⇒_ public

-- Const identifies objects that are terminal for this category
terminal : ∀ {ℓ a}{A : Set a}{P : MP ℓ} → A → P ⇒ Const A
terminal x = mk⇒ (λ _ → x) λ c~c' → λ {p} → PEq.refl

infixl 100 _∘_
_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃}{P : MP ℓ₁}{Q : MP ℓ₂}{R : MP ℓ₃} → Q ⇒ R → P ⇒ Q → P ⇒ R
_∘_ {P = P}{Q}{R} F G = mk⇒
  (λ p → apply F (apply G p))
  (λ c~c' →
    begin _
      ≡⟨ PEq.cong (λ e → apply F e) (monotone-comm G c~c') ⟩
    apply F (MP.monotone Q c~c' (apply G _))
      ≡⟨ monotone-comm F c~c' ⟩
    _ ∎
  )

id : ∀ {ℓ}(P : MP ℓ) → P ⇒ P
id P = mk⇒ Fun.id (λ _ → PEq.refl)

-- morphism equality
infixl 20 _⇒≡_
_⇒≡_  : ∀ {ℓ₁ ℓ₂}{P : MP ℓ₁}{Q : MP ℓ₂}(F G : P ⇒ Q) → Set _
_⇒≡_ {P = P}{Q} F G = ∀ {c}(p : P · c) → apply F p PEq.≡ apply G p

-- extensionality for morphisms
-- This should be provable from proof-irrelevance + extensionality.
⇒-Ext : ∀ (ℓ₁ ℓ₂ : Level) → Set _
⇒-Ext ℓ₁ ℓ₂ = ∀ {P : MP ℓ₁}{Q : MP ℓ₂}{F G : P ⇒ Q} → F ⇒≡ G → F PEq.≡ G

-- isomorphism
record _≅_ {ℓ}(P Q : MP ℓ) : Set (ℓ₁ ⊔ ℓ ⊔ ℓ₃) where
  field
    to    : P ⇒ Q
    from  : Q ⇒ P
    left-inv  : to ∘ from ⇒≡ id Q
    right-inv : from ∘ to ⇒≡ id P

module Properties where
  ∘-assoc : ∀ {p q r s}{P : MP p}{Q : MP q}{R : MP r}{S : MP s}
              {F : R ⇒ S}{G : Q ⇒ R}{H : P ⇒ Q} →
              F ∘ (G ∘ H) ⇒≡ (F ∘ G) ∘ H
  ∘-assoc _ = PEq.refl

  ∘-left-id : ∀ {P Q : MP ℓ₁}{F : P ⇒ Q} → (id Q) ∘ F ⇒≡ F
  ∘-left-id _ = PEq.refl

  ∘-right-id : ∀ {P Q : MP ℓ₁}{F : P ⇒ Q} → F ∘ (id P) ⇒≡ F
  ∘-right-id p = PEq.refl

module Product where
  -- within the category

  infixl 40 _⊗_
  _⊗_ : ∀ {ℓ₁ ℓ₂} → MP ℓ₁ → MP ℓ₂ → MP (ℓ₁ ⊔ ℓ₂)
  P ⊗ Q = mp
      (λ c → (P · c) × (Q · c))
      (record {
        monotone = λ{ c~c' (p , q) →
            MP.monotone P c~c' p
          , MP.monotone Q c~c' q
        };
        monotone-refl = λ _ → PEq.cong₂ _,_ (MP.monotone-refl P _) (MP.monotone-refl Q _) ;
        monotone-trans = λ _ _ _ → PEq.cong₂ _,_ (MP.monotone-trans P _ _ _) (MP.monotone-trans Q _ _ _)
      })

  ⟨_,_⟩ : ∀ {y p q}{Y : MP y}{P : MP p}{Q : MP q} → Y ⇒ P → Y ⇒ Q → Y ⇒ P ⊗ Q
  ⟨ F , G ⟩ = mk⇒
    (λ x → apply F x , apply G x)
    (λ c~c' → PEq.cong₂ _,_ (monotone-comm F c~c') (monotone-comm G c~c'))

  π₁ : ∀ {ℓ₁ ℓ₂}{P : MP ℓ₁}{Q : MP ℓ₂} → P ⊗ Q ⇒ P
  π₁ = mk⇒ (λ{ (pc , qc) → pc}) (λ c~c' → PEq.refl)

  π₂ : ∀ {ℓ₁ ℓ₂}{P : MP ℓ₁}{Q : MP ℓ₂} → P ⊗ Q ⇒ Q
  π₂ = mk⇒ (λ{ (pc , qc) → qc}) (λ c~c' → PEq.refl)

  swap : ∀ {ℓ₁ ℓ₂}(P : MP ℓ₁)(Q : MP ℓ₂) → P ⊗ Q ⇒ Q ⊗ P
  swap _ _ = mk⇒ Prod.swap λ c~c' → PEq.refl

  comm : ∀ {ℓ₁ ℓ₂ ℓ₃}(P : MP ℓ₁)(Q : MP ℓ₂)(R : MP ℓ₃) → (P ⊗ Q) ⊗ R ⇒ P ⊗ (Q ⊗ R)
  comm _ _ _ = mk⇒
    (λ{ ((p , q) , r) → p , (q , r) })
    (λ c~c' → PEq.refl)

  xmap : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}{P : MP ℓ₁}{Q : MP ℓ₂}{R : MP ℓ₃}{S : MP ℓ₄} →
         (F : P ⇒ R)(G : Q ⇒ S) → P ⊗ Q ⇒ R ⊗ S
  xmap F G = ⟨ F ∘ π₁ , G ∘ π₂ ⟩

  uncurry₁ : ∀ {ℓ₁ ℓ₂ ℓ₃}{A : Set ℓ₁}{P : MP ℓ₂}{Q : MP ℓ₃} →
             (A → P ⇒ Q) → (Const A ⊗ P ⇒ Q)
  uncurry₁ {A = A}{P}{Q} f = mk⇒
    (λ{ (a , p) → apply (f a) p })
    (λ{ c~c' {a , p} → monotone-comm (f a) c~c' })

  module ⊗-Properties where
    π₁-comm : ∀ {y p q}{Y : MP y}{P : MP p}{Q : MP q}{F : Y ⇒ P}{G : Y ⇒ Q} →
            π₁ ∘ ⟨ F , G ⟩ ⇒≡ F
    π₁-comm _ = PEq.refl

    π₂-comm : ∀ {y p q}{Y : MP y}{P : MP p}{Q : MP q}{F : Y ⇒ P}{G : Y ⇒ Q} →
            π₂ ∘ ⟨ F , G ⟩ ⇒≡ G
    π₂-comm _ = PEq.refl

    unique : ∀ {y p q}{Y : MP y}{P : MP p}{Q : MP q}{g : Y ⇒ (P ⊗ Q)} → ⟨ π₁ ∘ g , π₂ ∘ g ⟩ ⇒≡ g
    unique _ = PEq.refl

module Forall (funext : ∀ {a b} → PEq.Extensionality a b) where
  -- ∀-quantification over Set

  Forall : ∀ {ℓ₁ ℓ₂}{I : Set ℓ₁}(P : I → MP ℓ₂) → MP _
  Forall {I = I} P = mp
    (λ c → ∀ (i : I) → P i · c)
    (record {
      monotone = λ x x₁ i → MP.monotone (P i) x (x₁ i) ;
      monotone-refl = λ p → funext λ i → MP.monotone-refl (P i) (p i) ;
      monotone-trans = λ p c~c' c'~c'' → funext λ i → MP.monotone-trans (P i) (p i) c~c' c'~c'' })

module ListAll where
  -- quantification over the elements in a list

  open import Data.List
  import Data.List.All as All'
  open import Data.List.All.Properties.Extra

  All : ∀ {ℓ₁}{I : Set ℓ₁}(P : I → MP ℓ₂) → List I → MP _
  All P xs = mp
    (λ c → All'.All (λ x → P x · c) xs)
    (record {
      monotone = λ c~c' ps → All'.map (λ {i} x → MP.monotone (P i) c~c' x ) ps ;
      monotone-refl = λ p → (begin
        All'.map (λ {i} x → MP.monotone (P i) refl x) p
          ≡⟨ map-id p (λ i → MP.monotone-refl (P i)) ⟩
        p ∎) ;
      monotone-trans = λ p c~c' c'~c'' → (begin
       All'.map (λ {i} x → MP.monotone (P i) (trans c~c' c'~c'') x) p
         ≡⟨ map-cong p (λ i p → MP.monotone-trans (P i) p c~c' c'~c'') ⟩
       All'.map (λ {i} x → MP.monotone (P i) c'~c'' (MP.monotone (P i) c~c' x)) p
         ≡⟨ PEq.sym (map-map p) ⟩
       All'.map (λ {i} x → MP.monotone (P i) c'~c'' x) (All'.map (λ {i} x → MP.monotone (P i) c~c' x) p)
       ∎) })

module Exists where
  -- ∃-quantification over Set

  Exists : ∀ {ℓ₁ ℓ₂}{I : Set ℓ₁}(P : I → MP ℓ₂) → MP _
  Exists {I = I} P = mp (λ x → Prod.∃ λ (i : I) → P i · x) (record {
      monotone = λ{ c~c' (i , px) → i , MP.monotone (P i) c~c' px } ;
      monotone-refl = λ{
        (i , px) → PEq.cong (λ u → i , u) (MP.monotone-refl (P i) px) };
      monotone-trans = (λ {
        (i , px) p q → PEq.cong (λ u → i , u) (MP.monotone-trans (P i) px p q)})
    })

  elim : ∀ {ℓ₁ ℓ₂ ℓ₃}{I : Set ℓ₁}{P : I → MP ℓ₂}{Q : MP ℓ₃} →
         (∀ {i} → P i ⇒ Q) → Exists P ⇒ Q
  elim {P = P}{Q} F = mk⇒
    (λ{ (i , pi) → apply F pi})
    (λ{ c~c' {(i , pi)} → monotone-comm F c~c' })

  open Product
  ∃-⊗-comm : ∀ {ℓ₁ ℓ₂ ℓ₃}{I : Set ℓ₁}(P : I → MP ℓ₂)(Q : MP ℓ₃) →
             Exists (λ i → P i) ⊗ Q ⇒ Exists (λ i → P i ⊗ Q)
  ∃-⊗-comm _ _ = mk⇒
    (λ{ ((i , pi) , q) → (i , pi , q)})
    (λ c~c' → PEq.refl)

module Monoid where
  -- identifies _⊗_ as a tensor/monoidal product
  open Product

  -- associator
  assoc : ∀ {p q r}{P : MP p}{Q : MP q}{R : MP r} → (P ⊗ Q) ⊗ R ≅ P ⊗ (Q ⊗ R)
  assoc = record {
    to = mk⇒ (λ{ ((p , q) , r) → p , (q , r) }) (λ c~c' → PEq.refl) ;
    from = mk⇒ (λ{ (p , (q , r)) → (p , q) , r }) (λ c~c' → PEq.refl) ;
    left-inv = λ _ → PEq.refl ;
    right-inv = λ _ → PEq.refl }

  -- left unitor
  ⊗-left-id : ∀ {p}{P : MP p} → ⊤ ⊗ P ≅ P
  ⊗-left-id = record {
    to = π₂ {P = ⊤} ;
    from = ⟨ mk⇒ (λ x → Unit.tt) (λ c~c' → PEq.refl) , id _ ⟩ ;
    left-inv = λ p → PEq.refl ;
    right-inv = λ p → PEq.refl }

  -- right unitor
  ⊗-right-id : ∀ {p}{P : MP p} → P ⊗ ⊤ ≅ P
  ⊗-right-id = record {
    to = π₁ {Q = ⊤} ;
    from = ⟨ mk⇒ (λ {c} z → z) (λ c~c' → PEq.refl) , mk⇒ (λ {c} _ → Unit.tt) (λ c~c' → PEq.refl) ⟩ ;
    left-inv = λ p → PEq.refl ;
    right-inv = λ p → PEq.refl }

  -- TODO: coherence conditions

module Exponential
  (trans-assoc : ∀ {c c' c'' c'''}{p : c ≤ c'}{q : c' ≤ c''}{r : c'' ≤ c'''} →
                 trans (trans p q) r PEq.≡ trans p (trans q r))
  (trans-refl₁ : ∀ {c c'}{p : c ≤ c'} → trans refl p PEq.≡ p)
  (trans-refl₂ : ∀ {c c'}{p : c ≤ c'} → trans p refl PEq.≡ p)
  where

  -- for convencience we assume extensionality for morphisms here for now
  postulate ⇒-ext : ∀ {ℓ₁ ℓ₂} → ⇒-Ext ℓ₁ ℓ₂

  open Product

  -- the preorder that we have defined monotonicity by is itself
  -- a monotone predicate
  ≤mono : Carrier → MP _
  ≤mono c = mp (λ c' → c ≤ c' ) (record {
    monotone = flip trans  ;
    monotone-refl = λ _ → trans-refl₂ ;
    monotone-trans = λ _ _ _ → PEq.sym trans-assoc })

  -- ... such that we can define the notion of a monotone function as follows:
  Mono⇒ : ∀ {ℓ ℓ₂}(P : MP ℓ)(Q : MP ℓ₂)(c : Carrier) → Set _
  Mono⇒ P Q c = ≤mono c ⊗ P ⇒ Q
  -- the intuition here comes from the naive interpretation
  -- of the type of curry: (X ⊗ P ⇒ Q) → X ⇒ (Const (P ⇒ Q)).
  -- unfolding the return type you would get something like the following Agda type:
  --   ∀ c → X · c → (∀ c' → P · c' → Q · c')
  -- this is too weak, because c' and c are unrelated and thus we can't combine
  -- X · c and P · c' into a product (X ⊗ P) · c'.
  -- The above Mono⇒ fixes this by simply requiring the relation c ≤ c' as
  -- an additional argument.

  infixl 80 _^_
  _^_ : ∀ {ℓ₁ ℓ₂}(Q : MP ℓ₁)(P : MP ℓ₂) → MP _
  Q ^ P = mp
    (Mono⇒ P Q)
    (record {
      monotone = λ c~c' φ →
        mk⇒
          (λ p → apply φ (trans c~c' (Prod.proj₁ p) , Prod.proj₂ p))
          (λ{ c~c'' {w , p} → (begin
            apply φ (trans c~c' (MP.monotone (≤mono _) c~c'' w) , (MP.monotone P c~c'' p))
              ≡⟨ PEq.cong (λ u → apply φ (u , MP.monotone P c~c'' p)) (PEq.sym trans-assoc) ⟩
            apply φ (MP.monotone (≤mono _ ⊗ P) c~c'' (trans c~c' w , p))
              ≡⟨ monotone-comm φ c~c'' ⟩
            MP.monotone Q c~c'' (apply φ (trans c~c' w , p))
          ∎)});
      monotone-refl  = λ φ → ⇒-ext (λ p → PEq.cong (λ u → apply φ (u , (Prod.proj₂ p))) trans-refl₁);
      monotone-trans = λ φ w₀ w₁ → ⇒-ext λ p → PEq.cong (λ u → apply φ (u , Prod.proj₂ p)) trans-assoc
    })

  curry : ∀ {ℓ₁ ℓ₂ ℓ₃}{X : MP ℓ₁}{Y : MP ℓ₂}{Z : MP ℓ₃}(F : (X ⊗ Y) ⇒ Z) → X ⇒ (Z ^ Y)
  curry {X = X}{Y}{Z} F = mk⇒
    (λ xc → mk⇒
      (λ{ (w , yc) → apply F ((MP.monotone X w xc) , yc)})
      (λ{ c~c' {w , yc} → (begin
        apply F (MP.monotone X (trans w c~c') xc , MP.monotone Y c~c' yc)
          ≡⟨ PEq.cong (λ u → apply F (u , _)) (MP.monotone-trans X xc w c~c') ⟩
        apply F (MP.monotone X c~c' (MP.monotone X w xc) , MP.monotone Y c~c' yc)
          ≡⟨ monotone-comm F c~c' ⟩
        MP.monotone Z c~c' (apply F (MP.monotone X w xc , yc))
      ∎ )}))
    λ c~c' {xc} → ⇒-ext λ p →
      PEq.cong (λ u → apply F (u , _)) (PEq.sym (MP.monotone-trans X xc c~c' (Prod.proj₁ p)))

  ε : ∀ {ℓ₁ ℓ₂}{Y : MP ℓ₁}{Z : MP ℓ₂} → (Z ^ Y) ⊗ Y ⇒ Z
  ε {Y = Y}{Z} = mk⇒
    (λ zʸ×y → apply (Prod.proj₁ zʸ×y) (refl , Prod.proj₂ zʸ×y) )
    λ{ c~c' {φ@(F , p)} → (begin
      (apply F (trans c~c' refl , MP.monotone Y c~c' p))
        ≡⟨ PEq.cong (λ u → apply F (u , _)) trans-refl₂ ⟩
      (apply F (c~c' , MP.monotone Y c~c' p))
        ≡⟨ PEq.sym (PEq.cong (λ u → apply F (u , _)) trans-refl₁) ⟩
      (apply F (trans refl c~c' , MP.monotone Y c~c' p))
        ≡⟨ PEq.refl ⟩
      (apply F (MP.monotone (≤mono _ ⊗ Y) c~c' (refl , p)))
        ≡⟨ monotone-comm F c~c' ⟩
      MP.monotone Z c~c' (apply F (refl , p))
    ∎ )}

  uncurry : ∀ {ℓ₁ ℓ₂ ℓ₃}{X : MP ℓ₁}{Y : MP ℓ₂}{Z : MP ℓ₃}(F : X ⇒ (Z ^ Y)) → (X ⊗ Y) ⇒ Z
  uncurry {X = x}{Y}{Z} F = ε ∘ xmap F (id Y)
