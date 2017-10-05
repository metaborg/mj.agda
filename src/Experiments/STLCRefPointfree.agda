open import Relation.Binary.PropositionalEquality

module Experiments.STLCRefPointfree (funext : ∀ {a b} → Extensionality a b) where

open import Level
open import Data.Nat hiding (_^_)
import Data.Unit as Unit
open import Data.List
open import Data.List.Most
open import Data.Product hiding (curry; swap)
open import Data.Maybe as Maybe hiding (All)
open import Function as Fun using (case_of_)
import Relation.Binary.PropositionalEquality as PEq
import Relation.Binary.HeterogeneousEquality as H
open import Relation.Binary.PropositionalEquality.Extensionality funext
open PEq.≡-Reasoning

-- STLCRef typed syntax
------------------------------------------------------------------------

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

  mutual
    val-mono : ∀ {a Σ Σ'} → Σ ⊑ Σ' → Val' a Σ → Val' a Σ'
    val-mono ext unit = unit
    val-mono ext (clos e E) = clos e (env-mono ext E)
    val-mono ext (ref x) = ref (∈-⊒ x ext)

    val-mono-refl : ∀ {Σ a}(v : Val' a Σ) → val-mono ⊑-refl v ≡ v
    val-mono-refl unit = refl
    val-mono-refl (clos e E) = cong (clos e) (env-mono-refl E)
    val-mono-refl (ref x) = cong ref ∈-⊒-refl

    val-mono-trans : ∀ {a Σ Σ' Σ''}(v : Val' a Σ)(p : Σ' ⊒ Σ)(q : Σ'' ⊒ Σ') → val-mono (⊑-trans p q) v ≡ (val-mono q (val-mono p v))
    val-mono-trans unit p q = refl
    val-mono-trans (clos x E) p q = cong (clos x) (env-mono-trans E p q)
    val-mono-trans (ref x) p q = cong ref (∈-⊒-trans p q)

    env-mono : ∀ {Γ Σ Σ'} → Σ ⊑ Σ' → Env' Γ Σ → Env' Γ Σ'
    env-mono ext [] = []
    env-mono ext (px ∷ E) = (val-mono ext px) ∷ (env-mono ext E)

    env-mono-refl : ∀ {Γ Σ}(E : Env' Γ Σ) → env-mono ⊑-refl E ≡ E
    env-mono-refl [] = refl
    env-mono-refl (px ∷ E) = cong₂ _∷_ (val-mono-refl px) (env-mono-refl E)

    env-mono-trans : ∀ {Γ Σ Σ' Σ''}(E : Env' Γ Σ)(p : Σ' ⊒ Σ)(q : Σ'' ⊒ Σ') → env-mono (⊑-trans p q) E ≡ (env-mono q (env-mono p E))
    env-mono-trans [] p q = refl
    env-mono-trans (px ∷ E) p q = cong₂ _∷_ (val-mono-trans px p q) (env-mono-trans E p q)

    Env : Ctx → MP _
    Env Γ = mp (Env' Γ) (record {
      monotone = env-mono ;
      monotone-refl = env-mono-refl ;
      monotone-trans = env-mono-trans })

    Val : Ty → MP _
    Val a = mp (Val' a) (record {
      monotone = val-mono ;
      monotone-refl = val-mono-refl ;
      monotone-trans = val-mono-trans })

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
destructfun = mk⇒ (λ{ (clos x E) → _ , x , E}) λ{ c~c' {clos x E} → refl }

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
  (λ c~c' {p} → funext³ λ q ext μ →
    mcong {P = (Val (ref a))} refl H.refl
    (H.≡-to-≅ (
      cong (λ u → map-all _ μ all-∷ʳ u)
        (trans
          (sym (MP.monotone-trans (Val a) p c~c' _))
          (cong (λ u → (MP.monotone (Val a) u p)) ⊑-trans-assoc)
        )
    )) H.refl)

load : ∀ {a} → Val (ref a) ⇒ M (Val a)
load  {a} = mk⇒
  (λ v Σ₁ ext μ₁ → case v of λ{
    (ref x) → Σ₁ , ⊑-refl , μ₁ , (∈-all (∈-⊒ x ext) μ₁)
  })
  (λ{ c~c' {ref x} →
      funext³ λ p₁ q r →
      mcong {P = Val _} refl H.refl H.refl
        ((H.cong (λ u → ∈-all u r) (H.≡-to-≅ (sym (∈-⊒-trans c~c' q)))))
  })

store : ∀ {a} → (Val (ref a) ⊗ Val a) ⇒ M ⊤
store = mk⇒
  (λ x Σ₁ ext μ₁ → case x of λ{
    (ref l , v) → Σ₁ , ⊑-refl , (μ₁ All[ ∈-⊒ l ext ]≔' MP.monotone (Val _) ext v) , Unit.tt
  })
  (λ{ c~c' {ref x , v} →
    funext³ λ p q r →
    mcong {P = ⊤} refl H.refl
      (H.cong₂ (λ u v → r All[ u ]≔' v)
        (H.≡-to-≅ (sym (∈-⊒-trans c~c' q)))
        (H.≡-to-≅ (sym (MP.monotone-trans (Val _) v _ _))))
      H.refl
  })

-- environment manipulation
------------------------------------------------------------------------

envlookup : ∀ {a Γ} → a ∈ Γ → Env Γ ⇒ Val a
envlookup x = mk⇒ (λ E → lookup E x) λ{ c~c' {E} → sym (lem c~c' E x)}
  where
    lem : ∀ {Γ Σ Σ' a} → (p : Σ ⊑ Σ') → (E : Env' Γ Σ) → (e : a ∈ Γ) → val-mono p (lookup E e) ≡ lookup (env-mono p E) e
    lem p (px ∷ E) (here refl) = refl
    lem p (px ∷ E) (there e) = lem p E e

envcons : ∀ {a Γ} → Val a ⊗ Env Γ ⇒ Env (a ∷ Γ)
envcons = mk⇒ (uncurry _∷_) λ c~c' → refl

-- STLCRef interpreter; pointfree style
------------------------------------------------------------------------

open Exponential (sym ⊑-trans-assoc) ⊑-trans-refl ⊑-trans-refl'
open Strong

mutual
  interpclos : ∀ {a b} → Val (a ⟶ b) ⇒ M (Val b) ^ (Val a)
  interpclos = curry (
      elim (
        uncurry₁ eval
        ∘ (xmap (id (Const _)) (envcons ∘ Product.swap (Env _)(Val _)))
        ∘ Product.comm (Const _)(Env _)(Val _)
      )
      ∘ ∃-⊗-comm (λ Γ → Const _ ⊗ Env Γ)(Val _)
      ∘ xmap destructfun (id (Val _)))

  {-# TERMINATING #-}
  eval : ∀ {Γ a} → Expr Γ a → Env Γ ⇒ M (Val a)
  eval (var x) = η (Val _) ∘ envlookup x
  eval (ƛ e) = η (Val _) ∘ mkclos ∘ ⟨ terminal e , id (Env _) ⟩
  eval (app f e) =
    μ (Val _)
    ∘ fmap (ε ∘ xmap interpclos (id (Val _)))
    ∘ μ (Val _ ⊗ Val _)
    ∘ fmap (ts (Val _) (Val _))
    ∘ ts' (Val _) (M (Val _))
    ∘ ⟨ eval f , eval e ⟩
  eval unit = η (Val _) ∘ mkunit ∘ terminal Unit.tt
  eval (ref e) = bind (Val _) alloc ∘ eval e
  eval (! e) = bind (Val _) load ∘ eval e
  eval (e₁ ≔ e₂) =
      fmap mkunit
    ∘ μ ⊤
    ∘ fmap store
    ∘ μ ((Val _) ⊗ (Val _))
    ∘ fmap (ts' (Val _)(Val _))
    ∘ ts (M (Val _))(Val _)
    ∘ ⟨ eval e₁ , eval e₂ ⟩

module Examples where

  test : Expr [] unit
  test = let id = ƛ (var (here refl)) in app (ƛ (app id (var (here refl)))) unit

  test! : apply (eval test) [] [] ⊑-refl [] ≡ ([] , [] , [] , unit)
  test! = refl
