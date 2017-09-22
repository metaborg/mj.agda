open import Relation.Binary.PropositionalEquality

module Experiments.STLCRefNested (funext : ∀ {a b} → Extensionality a b) where

open import Level
open import Data.Nat
import Data.Unit as Unit
open import Data.List
open import Data.List.Most
open import Data.Product
open import Data.Maybe as Maybe hiding (All)
open import Function as Fun using (case_of_)
import Relation.Binary.PropositionalEquality as PEq
open PEq.≡-Reasoning

data Ty : Set where
  unit : Ty
  _⟶_ : (a b : Ty) → Ty
  ref  : Ty → Ty

open import Experiments.Category (⊑-preorder {A = Ty})
open Product
open Exists

Ctx     = List Ty
StoreTy = List Ty

data Expr (Γ : List Ty) : Ty → Set where
  var : ∀ {t} → t ∈ Γ → Expr Γ t
  ƛ     : ∀ {a b} → Expr (a ∷ Γ) b → Expr Γ (a ⟶ b)
  app   : ∀ {a b} → Expr Γ (a ⟶ b) → Expr Γ a → Expr Γ b
  unit  : Expr Γ unit
  ref   : ∀ {t} → Expr Γ t → Expr Γ (ref t)
  !_    : ∀ {t} → Expr Γ (ref t) → Expr Γ t
  _≔_   : ∀ {t} → Expr Γ (ref t) → Expr Γ t → Expr Γ unit

module Values where
  mutual
    Env' : (Γ : Ctx)(Σ : StoreTy) → Set
    Env' Γ Σ = All (λ t → Val' t Σ) Γ

    data Val' : Ty → List Ty → Set where
      unit   : ∀ {Σ} → Val' unit Σ
      clos   : ∀ {Σ Γ a b} → Expr (a ∷ Γ) b → Env' Γ Σ → Val' (a ⟶ b) Σ
      ref    : ∀ {Σ t} → t ∈ Σ → Val' (ref t) Σ

  weaken-all : ∀ {i}{A : Set i}{j}{B : Set j}{xs : List B}
                {k}{C : B → List A → Set k}( wₐ : ∀ {x} {bs cs} → bs ⊑ cs → C x bs → C x cs) →
                ∀ {bs cs} → bs ⊑ cs → All (λ x → C x bs) xs → All (λ x → C x cs) xs
  weaken-all wₐ ext x = map-all (λ y → wₐ ext y) x

  mutual
    Env : Ctx → MP _
    Env Γ = mp (Env' Γ) (record {
      monotone = {!!} ;
      monotone-refl = {!!} ;
      monotone-trans = {!!} })

    Val : Ty → MP _
    Val a = mp (Val' a) (record {
      monotone = {!!} ;
      monotone-refl = {!!} ;
      monotone-trans = {!!} })

open Values
open import Experiments.StrongMonad Ty Val funext

mkclos : ∀ {Γ a b} → Const (Expr (a ∷ Γ) b) ⊗ Env Γ ⇒ Val (a ⟶ b)
mkclos = {!!}

mkunit : ⊤ ⇒ Val unit
mkunit = mk⇒ (λ _ → Values.unit) λ c~c' → {!!}

destructfun : ∀ {a b} → Val (a ⟶ b) ⇒ (Exists (λ Γ → Const (Expr (a ∷ Γ) b) ⊗ Env Γ))
destructfun = mk⇒ (λ{ (clos x E) → _ , x , E}) λ c~c' → {!!}

alloc : ∀ {a} → Val a ⇒ M (Val (ref a))
alloc {a} = mk⇒
  (λ v Σ₁ ext μ₁ →
    let ext' = ∷ʳ-⊒ a Σ₁ in
      (Σ₁ ∷ʳ a) ,
      ext' ,
      ((map-all (MP.monotone (Val _) ext') μ₁) all-∷ʳ MP.monotone (Val _) (⊑-trans ext ext') v) ,
      ref (∈-∷ʳ Σ₁ a))
  (λ c~c' → {!!})

load : ∀ {a} → Val (ref a) ⇒ M (Val a)
load  {a} = mk⇒
  (λ v Σ₁ ext μ₁ → case v of λ{
    (ref x) → Σ₁ , ⊑-refl , μ₁ , (∈-all (∈-⊒ x ext) μ₁)
  })
  (λ c~c' → {!!})

store : ∀ {a} → (Val (ref a) ⊗ Val a) ⇒ M ⊤
store = mk⇒
  (λ x Σ₁ ext μ₁ → case x of λ{
    (ref l , v) → Σ₁ , ⊑-refl , (μ₁ All[ ∈-⊒ l ext ]≔' MP.monotone (Val _) ext v) , Unit.tt
  })
  (λ c~c' → {!!})

envlookup : ∀ {a Γ} → a ∈ Γ → Env Γ ⇒ Val a
envlookup = {!!}

{-# NON_TERMINATING #-}
eval : ∀ {Γ a} → Expr Γ a → Env Γ ⇒ M (Val a)
eval (var x) = η (Val _) ∘ envlookup x
eval (ƛ e) = η (Val _) ∘ mkclos ∘ ⟨ {!!} , id (Env _) ⟩
eval (app f e) =
  {!!}
  ∘ μ (Val _ ⊗ Val _)
  ∘ fmap (ts (Val _) (Val _))
  ∘ ts' (Val _) (M (Val _))
  ∘ ⟨ eval f , eval e ⟩
eval unit = η (Val _) ∘ mkunit ∘ terminal
eval (ref e) = μ (Val _) ∘ fmap alloc ∘ eval e
eval (! e) = μ (Val _) ∘ fmap load ∘ eval e
eval (e₁ ≔ e₂) =
    fmap mkunit
  ∘ μ ⊤
  ∘ fmap store
  ∘ μ ((Val _) ⊗ (Val _))
  ∘ fmap (ts' (Val _)(Val _))
  ∘ ts (M (Val _))(Val _)
  ∘ ⟨ eval e₁ , eval e₂ ⟩

