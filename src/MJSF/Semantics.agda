open import Data.Nat hiding (_^_ ; _+_)
open import Data.List.Most
open import Data.Integer
open import Data.Unit
open import Data.Empty
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Function
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Star hiding (return ; _>>=_ ; map)

module MJSF.Semantics (k : ℕ) where

open import MJSF.Syntax k
open import MJSF.Values k
open import MJSF.Monad k
open import ScopeGraph.ScopesFrames k Ty
open import Common.Weakening

module Semantics (g : Graph) where

  open SyntaxG g
  open ValuesG g
  open MonadG g
  open UsesVal Valᵗ valᵗ-weaken renaming (getFrame to getFrame') public

  -----------------
  -- AUXILIARIES --
  -----------------

  default : {Σ : List Scope} → (t : VTy) → Val t Σ
  default int     = num (ℤ.pos 0)
  default (ref s) = null
  default void    = void

  defaults : ∀ {fs : List Ty}{Σ} → All (#v (λ _ → ⊤)) fs → Slots fs Σ
  defaults {[]}          []           = []
  defaults {vᵗ t ∷ fs} (#v' _ ∷ ts) = vᵗ (default t) ∷ defaults {fs} ts

  override : ∀ {s Σ oms} →
             All (#m (λ ts t → (s ↦ (mᵗ ts t)) × Meth s ts t)) oms →
             M s (λ _ → ⊤) Σ
  override [] = return tt
  override (#m' (p , m) ∷ oms) =
    getFrame >>= λ f →
    setv p (mᵗ f m) >>= λ _ →
    override oms

  init-obj : ∀ {sʳ s s' Σ} → Class sʳ s → Inherits s s' → M sʳ (Frame s) Σ
  init-obj (class0 ⦃ shape ⦄ ms fs oms) (obj _)
    = getFrame >>= λ f →
      initι _ ⦃ shape ⦄ (λ fc → (map-all (λ{ (#m' m) → mᵗ fc m }) ms) ++-all (defaults fs)) (f ∷ []) >>= λ f' →
      (usingFrame f' (override oms) ^ f') >>= λ{ (_ , f') → return f' }
  init-obj (class0 ⦃ shape ⦄ _ _ _) (super ⦃ shape' ⦄ _) with (trans (sym shape) shape')
  ... | ()
  init-obj (class1 p ⦃ shape ⦄ ms fs oms) (super ⦃ shape' ⦄ x) with (trans (sym shape) shape')
  ... | refl =
    getv p >>= λ{ (cᵗ class' ic f') →
    (usingFrame f' (init-obj class' x) ^ f') >>= λ{ (f , f') →
    initι _ ⦃ shape ⦄ (λ fc → (map-all (λ{ (#m' m) → mᵗ fc m }) ms) ++-all (defaults fs)) (f' ∷ f ∷ []) >>= λ f'' →
    (usingFrame f'' (override oms) ^ f'') >>= λ{ (_ , f'') →
    return f'' }}}
  init-obj (class1 _ ⦃ shape ⦄ _ _ _) (obj _ ⦃ shape' ⦄) with (trans (sym shape) shape')
  ... | ()

  _>>=ᶜ_     :  ∀ {s s' s'' r Σ} →
               M s (λ Σ → Val r Σ ⊎ Frame s' Σ) Σ →
               (∀ {Σ'} → Frame s' Σ' → M s (λ Σ → Val r Σ ⊎ Frame s'' Σ) Σ') →
               M s (λ Σ → Val r Σ ⊎ Frame s'' Σ) Σ
  (m >>=ᶜ f) = m >>= λ{
      (inj₁ v) → return (inj₁ v) ;
      (inj₂ fr) → f fr
    }

  continue : ∀ {s r Σ} → M s (λ Σ → Val r Σ ⊎ Frame s Σ) Σ
  continue = fmap inj₂ getFrame

  mutual
    eval    :  ℕ → ∀ {t s Σ} → Expr s t → M s (Val t) Σ
    eval zero _ =
      timeoutᴹ
    eval (suc k) (upcast σ e) =
      coerceᴹ σ (eval k e)
    eval (suc k) (num x) =
      return (num x)
    eval (suc k) (iop x l r) =
      eval k l >>= λ{ (num il) →
      eval k r >>= λ{ (num ir) →
      return (num (il + ir)) }}
    eval (suc k) null =
      return null
    eval (suc k) (var x) =
      getv x >>= λ{ (vᵗ v) →
      return v }
    eval (suc k) (new x) =
      getv x >>= λ{ (cᵗ class ic f) →
      usingFrame f (init-obj class ic) >>= λ{ f' →
      return (ref f') }}
    eval (suc k) (get e p) =
      eval k e >>= λ{ null → raise ; (ref f) →
      usingFrame f (getv p) >>= λ{ (vᵗ v) →
      return v }}
    eval (suc k) (call e p args) =
      eval k e >>= λ { null → raise ; (ref f) →
      usingFrame f (getv p) >>= λ{ (mᵗ f' (meth s ⦃ shape ⦄ b)) →
      (eval-args k args ^ f') >>= λ{ (slots , f') →
      init s ⦃ shape ⦄ slots (f' ∷ []) >>= λ f' →
      usingFrame f' (eval-body k b) }}}
    eval (suc k) (this p e) =
      getf p >>= λ f →
      usingFrame f (getl e) >>= λ f' →
      return (ref f')

    eval-args : ℕ → ∀ {s ts Σ} → All (Expr s) ts → M s (Slots (map vᵗ ts)) Σ
    eval-args zero _ = timeoutᴹ
    eval-args (suc k) [] = return []
    eval-args (suc k) (e ∷ es) =
      eval k e >>= λ v →
      (eval-args k es ^ v) >>= λ{ (slots , v) →
      return (vᵗ v ∷ slots) }

    eval-stmt : ℕ → ∀ {s s' r Σ} → Stmt s r s' → M s (λ Σ → Val r Σ ⊎ Frame s' Σ) Σ
    eval-stmt zero _ = timeoutᴹ
    eval-stmt (suc k) (do e) = eval k e >>= λ _ → continue
    eval-stmt (suc k) (ifz c t e) =
      eval k c >>= λ{
        (num (+ zero)) → eval-stmt k t
      ; (num i) → eval-stmt k e }
    eval-stmt (suc k) (set e x e') =
      eval k e >>= λ{ null → raise ; (ref f) →
      (eval k e' ^ f) >>= λ{ (v , f) →
      usingFrame f (setv x (vᵗ v)) >>= λ _ → continue }}
    eval-stmt (suc k) (loc s t) =
      getFrame >>= λ f → fmap inj₂ (init s (vᵗ (default t) ∷ []) (f ∷ []))
    eval-stmt (suc k) (asgn x e) =
      eval k e >>= λ{ v →
      setv x (vᵗ v) >>= λ _ → continue }
    eval-stmt (suc k) (block stmts) =
      eval-stmts k stmts >>= λ{ _ →
      continue }
    eval-stmt (suc k) (ret e) =
      eval k e >>= λ{ v →
      return (inj₁ v) }

    eval-stmts : ℕ → ∀ {s r s' Σ} → Stmts s r s' → M s (λ Σ → Val r Σ ⊎ Frame s' Σ) Σ
    eval-stmts zero _ =
      timeoutᴹ
    eval-stmts (suc k) ε =
      continue
    eval-stmts (suc k) (stmt ◅ stmts) =
      eval-stmt k stmt >>=ᶜ λ f' →
      usingFrame f' (eval-stmts k stmts)

    eval-body : ℕ → ∀ {s t Σ} → Body s t → M s (Val t) Σ
    eval-body zero _ =
      timeoutᴹ
    eval-body (suc k) (body stmts e) =
      eval-stmts k stmts >>= λ{
        (inj₁ v)  → return v
      ; (inj₂ fr) → usingFrame fr (eval k e) }
    eval-body (suc k) (body-void stmts) =
      eval-stmts k stmts >>= λ _ →
      return void

  eval-program : ℕ → ∀ {sʳ t} → Program sʳ t → Res (∃ λ Σ' → (Heap Σ' × Val t Σ'))
  eval-program k (program _ ⦃ shape ⦄ cs b) =
    let (f₀ , h₀) = initFrameι _ (λ f → map-all (λ{ (#c' (c , _ , ic)) → cᵗ c ic f }) cs) [] []
    in case (eval-body k b f₀ h₀) of λ{
         (ok (Σ' , h' , v , _)) → ok (Σ' , h' , v)
       ; timeout → timeout
       ; nullpointer → nullpointer }

  -- a few predicates on programs:
  -- ... saying it will terminate succesfully in a state where P holds
  _⇓⟨_⟩_ : ∀ {sʳ a} → Program sʳ a → ℕ → (P : ∀ {W} → Val a W → Set) → Set
  p ⇓⟨ k ⟩ P with eval-program k p
  ... | nullpointer = ⊥
  ... | timeout = ⊥
  ... | ok (_ , _ , v) = P v

  -- ...saying it will raise an exception in a state where P holds
  _⇓⟨_⟩!_ : ∀ {sʳ a} → Program sʳ a → ℕ → (P : ∀ {W} → Val a W → Set) → Set
  p ⇓⟨ k ⟩! P with eval-program k p
  ... | nullpointer = ⊤
  ... | timeout = ⊥
  ... | ok (_ , _ , v) = ⊥
