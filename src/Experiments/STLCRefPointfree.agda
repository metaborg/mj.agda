open import Relation.Binary.PropositionalEquality

module Experiments.STLCRefPointfree (funext : ∀ {a b} → Extensionality a b) where

open import Level
open import Data.Nat hiding (_^_)
import Data.Unit as Unit
open import Data.List
open import Data.List.Most
open import Data.Product hiding (curry)
open import Data.Maybe as Maybe hiding (All)
open import Function as Fun using (case_of_)
import Relation.Binary.PropositionalEquality as PEq
open PEq.≡-Reasoning

-- STLCRef typed syntax
------------------------------------------------------------------------

data Ty : Set where
  unit : Ty
  _⟶_ : (a b : Ty) → Ty
  ref  : Ty → Ty

open import Experiments.Category (⊑-preorder {A = Ty})
open Product hiding (fmap)
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

  mutual
    val-mono : ∀ {a Σ Σ'} → Σ ⊑ Σ' → Val' a Σ → Val' a Σ'
    val-mono ext unit = unit
    val-mono ext (clos e E) = clos e (env-mono ext E)
    val-mono ext (ref x) = ref (∈-⊒ x ext)

    env-mono : ∀ {Γ Σ Σ'} → Σ ⊑ Σ' → Env' Γ Σ → Env' Γ Σ'
    env-mono ext [] = []
    env-mono ext (px ∷ E) = (val-mono ext px) ∷ (env-mono ext E)

    Env : Ctx → MP _
    Env Γ = mp (Env' Γ) (record {
      monotone = env-mono ;
      monotone-refl = λ p → {!!} ;
      monotone-trans = λ p c~c' c'~c'' → {!!} })

    Val : Ty → MP _
    Val a = mp (Val' a) (record {
      monotone = val-mono ;
      monotone-refl = {!!} ;
      monotone-trans = {!!} })

open Values
open import Experiments.StrongMonad Ty Val funext

-- Val constructors
------------------------------------------------------------------------

mkclos : ∀ {Γ a b} → Const (Expr (a ∷ Γ) b) ⊗ Env Γ ⇒ Val (a ⟶ b)
mkclos = mk⇒ (λ{ (e , E) → clos e E}) λ c~c' → refl

mkunit : ⊤ ⇒ Val unit
mkunit = mk⇒ (λ _ → Values.unit) λ c~c' → refl

-- destructors
------------------------------------------------------------------------

destructfun : ∀ {a b} → Val (a ⟶ b) ⇒ (Exists (λ Γ → Const (Expr (a ∷ Γ) b) ⊗ Env Γ))
destructfun = mk⇒ (λ{ (clos x E) → _ , x , E}) λ c~c' → {!!}

-- state manipulation
------------------------------------------------------------------------

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

-- environment manipulation
------------------------------------------------------------------------

envlookup : ∀ {a Γ} → a ∈ Γ → Env Γ ⇒ Val a
envlookup x = mk⇒ (λ E → lookup E x) λ c~c' → {!!}

envcons : ∀ {a Γ} → Val a ⊗ Env Γ ⇒ Env (a ∷ Γ)
envcons = mk⇒ (uncurry _∷_) λ c~c' → refl

-- STLCRef interpreter; pointfree style
------------------------------------------------------------------------

open Exponential (sym ⊑-trans-assoc) ⊑-trans-refl ⊑-trans-refl'

mutual
  interpclos : ∀ {a b} → Val (a ⟶ b) ⇒ M (Val b) ^ (Val a)
  interpclos = curry (
      elim (
        uncurry₁ eval
        ∘ (Product.fmap (id (Const _)) (envcons ∘ Product.swap (Env _)(Val _)))
        ∘ Product.comm (Const _)(Env _)(Val _)
      )
      ∘ ∃-⊗-comm (λ Γ → Const _ ⊗ Env Γ)(Val _)
      ∘ Product.fmap destructfun (id (Val _)))

  {-# NON_TERMINATING #-}
  eval : ∀ {Γ a} → Expr Γ a → Env Γ ⇒ M (Val a)
  eval (var x) = η (Val _) ∘ envlookup x
  eval (ƛ e) = η (Val _) ∘ mkclos ∘ ⟨ terminal e , id (Env _) ⟩
  eval (app f e) =
    μ (Val _)
    ∘ fmap (ε ∘ Product.fmap interpclos (id (Val _)))
    ∘ μ (Val _ ⊗ Val _)
    ∘ fmap (ts (Val _) (Val _))
    ∘ ts' (Val _) (M (Val _))
    ∘ ⟨ eval f , eval e ⟩
  eval unit = η (Val _) ∘ mkunit ∘ terminal Unit.tt
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

