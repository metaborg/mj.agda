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
open import ScopesFrames.ScopesFrames k Ty
open import Common.Weakening

-- This file contains the definitional interpreter for MJ using scopes
-- and frames, described in Section 5 of the paper.

module Semantics (g : Graph) where

  open SyntaxG g
  open ValuesG g
  open MonadG g
  open UsesVal Valᵗ valᵗ-weaken renaming (getFrame to getFrame') public


  -----------------
  -- AUXILIARIES --
  -----------------

  -- The interpreter relies on a number of auxiliary function.  We
  -- briefly summarize each.

  -- In Java (and MJ), each field member of an object is initialized
  -- to have a default value.  The `default` function defines a
  -- default value for each value type in MJ.

  default : {Σ : List Scope} → (t : VTy) → Val t Σ
  default int     = num (+ 0)
  default (ref s) = null
  default void    = void

  -- An alias for mapping `default` over a list of well-typed values:

  defaults : ∀ {fs : List Ty}{Σ} → All (#v (λ _ → ⊤)) fs → Slots fs Σ
  defaults fs = map-all (λ{ (#v' {t} _) → vᵗ (default t) }) fs

  -- `override` overrides methods in parent objects by overwriting
  -- method slots in super class frames by overriding child methods.
  --
  -- This notion of overriding does not straightforwardly scale to
  -- deal with `super`, but `super` is not a part of MJ.  See the
  -- paper or the MJ semantics in the appendix of this artifact for
  -- discussion and inspiration for how to represent class methods
  -- separately from object representations.

  override : ∀ {s Σ oms} →
             All (#m (λ ts t → (s ↦ (mᵗ ts t)) × Meth s ts t)) oms →
             M s (λ _ → ⊤) Σ
  override [] =
    return tt
  override (#m' (p , m) ∷ oms) =
    getFrame >>= λ f →
    setv p (mᵗ f m) >>= λ _ →
    override oms

  -- `init-obj` takes as input a class definition and a witness that
  -- the class has a finite inheritance chain.  The function is
  -- structurally recursive over the inheritance chain finity witness.
  --
  -- Each object is initialized by using the `initι` function, which
  -- allows us to refer to the "self" frame and store it in method
  -- definitions (i.e., the `fc` passed to the method value
  -- constructor `mᵗ` in `map-all` below).
  --
  -- Method slots are initialized using the method members in the
  -- class definition.  Field slots are initialized using `defaults`
  -- defined above.
  --
  -- After frame initialization, overrides are applied by using
  -- `override` defined above.
  --
  -- `init-obj` is assumed to be invoked in the context of the root
  -- frame, which all objects are linked to (because all scopes have
  -- an edge to the root scope).

  init-obj : ∀ {sʳ s s' Σ} → Class sʳ s → Inherits s s' → M sʳ (Frame s) Σ
  init-obj (class0 ⦃ shape ⦄ ms fs oms) (obj _)
    = getFrame >>= λ f →
      initι _ ⦃ shape ⦄ (λ fc → (map-all (λ{ (#m' m) → mᵗ fc m }) ms) ++-all (defaults fs)) (f ∷ []) >>= λ f' →
      (usingFrame f' (override oms) ^ f') >>= λ{ (_ , f') → return f' }
  init-obj (class0 ⦃ shape ⦄ _ _ _) (super ⦃ shape' ⦄ _)
    with (trans (sym shape) shape')
  ...  | () -- absurd case: the scope shapes of `class0` and `super` do not match
  init-obj (class1 p ⦃ shape ⦄ ms fs oms) (super ⦃ shape' ⦄ x)
    with (trans (sym shape) shape')
  ...  | refl =
    getv p >>= λ{ (cᵗ class' ic f') →
    (usingFrame f' (init-obj class' x) ^ f') >>= λ{ (f , f') →
    initι _ ⦃ shape ⦄ (λ fc → (map-all (λ{ (#m' m) → mᵗ fc m }) ms) ++-all (defaults fs)) (f' ∷ f ∷ []) >>= λ f'' →
    (usingFrame f'' (override oms) ^ f'') >>= λ{ (_ , f'') →
    return f'' }}}
  init-obj (class1 _ ⦃ shape ⦄ _ _ _) (obj _ ⦃ shape' ⦄)
    with (trans (sym shape) shape')
  ...  | () -- absurd case: the scope shapes of `class1` and `obj` do not match


  -------------------------
  -- EARLY RETURNS MONAD --
  -------------------------

  -- In order to deal with early returns, we define a specialized bind
  -- which stops evaluation and returns the yielded value.

  _>>=ᶜ_     :  ∀ {s s' s'' r Σ} →
               M s (λ Σ → Val r Σ ⊎ Frame s' Σ) Σ →
               (∀ {Σ'} → Frame s' Σ' → M s (λ Σ → Val r Σ ⊎ Frame s'' Σ) Σ') →
               M s (λ Σ → Val r Σ ⊎ Frame s'' Σ) Σ
  (m >>=ᶜ f) = m >>= λ{
      (inj₁ v) → return (inj₁ v) ;
      (inj₂ fr) → f fr
    }

  -- Continue is used to indicate that evaluation should continue.
  
  continue : ∀ {s r Σ} → M s (λ Σ → Val r Σ ⊎ Frame s Σ) Σ
  continue = fmap inj₂ getFrame

  mutual

    ---------------------------
    -- EXPRESSION EVALUATION --
    ---------------------------

    eval    :  ℕ → ∀ {t s Σ} → Expr s t → M s (Val t) Σ
    eval zero _ =
      timeoutᴹ
    eval (suc k) (upcast σ e) =
      coerceᴹ σ (eval k e)  -- upcasts coerce the object representation
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
      usingFrame f (getv p) >>= λ{ (mᵗ f' (meth s ⦃ shape ⦄ b)) →  -- f' is the "self"
      (eval-args k args ^ f') >>= λ{ (slots , f') →
      init s ⦃ shape ⦄ slots (f' ∷ []) >>= λ f'' →  -- f' is the static link of the method call frame
      usingFrame f'' (eval-body k b) }}}
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


    --------------------------
    -- STATEMENT EVALUATION --
    --------------------------

    -- The following functions use the early returns monadic bind and
    -- `continue` operation defined above.

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
      getFrame >>= λ f →
      fmap inj₂ (init s (vᵗ (default t) ∷ []) (f ∷ [])) -- initializes a new local variable frame
    eval-stmt (suc k) (asgn x e) =
      eval k e >>= λ{ v →
      setv x (vᵗ v) >>= λ _ →
      continue }
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


    ---------------------
    -- BODY EVALUATION --
    ---------------------

    -- Defined in terms of statement evaluation; handles early returns:

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


  ------------------------
  -- PROGRAM EVALUATION --
  ------------------------

  -- Program evaluation first initializes the root frame to store all
  -- class definitions, and subsequently evaluates the program main
  -- function in the context of this root scope.
  --
  -- We use `initι` to initialize the root frame since class
  -- definition values (`cᵗ`) store a pointer to the root frame, i.e.,
  -- slots in the root frame are self-referential.

  eval-program : ℕ → ∀ {sʳ t} → Program sʳ t → Res (∃ λ Σ' → (Heap Σ' × Val t Σ'))
  eval-program k (program _ ⦃ shape ⦄ cs b) =
    let (f₀ , h₀) = initFrameι _ (λ f → map-all (λ{ (#c' (c , _ , ic)) → cᵗ c ic f }) cs) [] []
    in case (eval-body k b f₀ h₀) of λ{
         (ok (Σ' , h' , v , _)) → ok (Σ' , h' , v)
       ; timeout → timeout
       ; nullpointer → nullpointer }

  -- For the purpose of running the interpreter on test programs, we
  -- introduce some short-hand notation:

  -- The program will terminate succesfully in a state where p holds
  _⇓⟨_⟩_ : ∀ {sʳ a} → Program sʳ a → ℕ → (p : ∀ {Σ} → Val a Σ → Set) → Set
  p ⇓⟨ k ⟩ P with eval-program k p
  ... | nullpointer = ⊥
  ... | timeout = ⊥
  ... | ok (_ , _ , v) = P v

  -- The program will raise an exception in a state where p holds
  _⇓⟨_⟩!_ : ∀ {sʳ a} → Program sʳ a → ℕ → (p : ∀ {Σ} → Val a Σ → Set) → Set
  p ⇓⟨ k ⟩! P with eval-program k p
  ... | nullpointer = ⊤
  ... | timeout = ⊥
  ... | ok (_ , _ , v) = ⊥
