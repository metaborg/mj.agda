open import Data.Nat hiding (_^_)
open import Data.List.Most
open import Data.Product hiding (map)
open import Data.Unit
open import Data.String
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Relation.Unary.Weakening.ListPrefix

-- This file contains the definition of monads used for computation in
-- the definitional interpreter for MJ using scopes and frames,
-- described in Section 5 of the paper.

module ScopesFrames.FrameHeap.Monad.FrameHeap (Ty    : ℕ → Set)
                                              (Name  : Set)
                                              (Label : Set)
                                              where

open import ScopesFrames.ScopeGraph Ty Name Label
open Graph

module MonadWithVal {g : Graph}
                    (Val : Ty (ı g) → List (Scope (ı g)) → Set)
                    (Val-Wk : {t : Ty (ı g)} → Wk (Val t)) where

  open import ScopesFrames.FrameHeap Ty Name Label
  open UsesGraph {g}
  open UsesVal Val Val-Wk renaming (getFrame to getFrame')
  open import Relation.Unary.Weakening.ListPrefix

  -- Computations may either time out, raise a null-pointer exception,
  -- or successfully terminate to produce a result:

  data Res (A : Set) : Set where
    timeout-res : Res A
    err : String → Res A
    ok : (x : A) → Res A

  -- The monad is similar to the monad used for STLCSF, except it uses
  -- `Res` instead of `Maybe`:

  M : (s : Scope (ı g)) → (List (Scope (ı g)) → Set) → List (Scope (ı g)) → Set
  M s p Σ = Frame s Σ → Heap Σ → Res (∃ λ Σ' → (Heap Σ' × p Σ' × Σ ⊑ Σ'))

  -- We define some usual monad operations:

  return     :  ∀ {s Σ}{P : List (Scope (ı g)) → Set} → P Σ → M s P Σ
  return v f h = ok (_ , h , v , ⊑-refl)

  fmap : ∀ {P Q : List (Scope (ı g)) → Set}{Γ Σ} → (∀ {Σ} → P Σ → Q Σ) → M Γ P Σ → M Γ Q Σ
  fmap g m f h
    with (m f h)
  ...  | timeout-res = timeout-res
  ...  | err reason = err reason
  ...  | ok (Σ' , h' , v' , ext') = ok (Σ' , h' , g v' , ext')

  join : ∀ {P : List (Scope (ı g)) → Set}{Γ Σ} → M Γ (M Γ P) Σ → M Γ P Σ
  join m f h
    with (m f h)
  ...  | timeout-res = timeout-res
  ...  | err reason = err reason
  ...  | ok (Σ' , h' , m' , ext')
       with (m' (wk ext' f) h')
  ...     | timeout-res = timeout-res
  ...     | err reason = err reason
  ...     | ok (Σ'' , h'' , v'' , ext'') = ok ((Σ'' , h'' , v'' , ext' ⊚ ext''))

  _>>=_     :  ∀ {s Σ}{P Q : List (Scope (ı g)) → Set} →
               M s P Σ → (∀ {Σ'} → P Σ' → M s Q Σ') → M s Q Σ
  (a >>= b) = join (fmap b a)

  -- To program in dependent-passing style, we use the variant of
  -- monadic strength also used for STLCSF.

  infixl 3 _^_
  _^_  :  ∀ {Σ Γ}{P Q : List (Scope (ı g)) → Set} ⦃ w : Wk Q ⦄ →
          M Γ P Σ → Q Σ → M Γ (P ⊗ Q) Σ
  (a ^ x) f h
    with (a f h)
  ...  | timeout-res = timeout-res
  ...  | err reason = err reason
  ...  | ok (Σ , h' , v , ext) = ok (Σ , h' , (v , wk ext x) , ext)

  -- The remaining definitions in this file are straightforward
  -- monadic liftings of the coercion function from `MJSF.Values` and
  -- of the frame operations.

  getFrame   :  ∀ {s Σ} → M s (Frame s) Σ
  getFrame f = return f f

  usingFrame  :  ∀ {s s' Σ}{P : List (Scope (ı g)) → Set} → Frame s Σ → M s P Σ → M s' P Σ
  usingFrame f a _ = a f

  timeout    :  ∀ {s Σ}{P : List (Scope (ı g)) → Set} → M s P Σ
  timeout _ _ = timeout-res

  raise : ∀ {s Σ}{P : List (Scope (ı g)) → Set} → String → M s P Σ
  raise reason _ _ = err reason

  init : ∀ {Σ s' ds es} → (s : (Scope (ı g))) → ⦃ shape : nodeOf♭ g s ≡ (ds , es) ⦄ →
         Slots ds Σ → Links es Σ → M s' (Frame s) Σ
  init {Σ} s slots links _ h
    with (initFrame s slots links h)
  ...  | (f' , h') = ok (_ , h' , f' , ∷ʳ-⊒ s Σ)

  initι : ∀ {Σ s' ds es} → (s : Scope (ı g)) → ⦃ shape : nodeOf♭ g s ≡ (ds , es) ⦄ →
               (Frame s (Σ ∷ʳ s) → Slots ds (Σ ∷ʳ s)) → Links es Σ → M s' (Frame s) Σ
  initι {Σ} s slots links _ h
    with (initFrameι s slots links h)
  ...  | (f' , h') = ok (_ , h' , f' , ∷ʳ-⊒ s Σ)

  getv : ∀ {s t Σ} → (g ⊢♭ s ↦ t) → M s (Val t) Σ
  getv p f h = return (getVal p f h) f h

  getf : ∀ {s s' Σ} → (g ⊢♭ s ⟶ s')  → M s (Frame s') Σ
  getf p f h = return (getFrame' p f h) f h

  getd : ∀ {s t Σ} → t ∈ declsOf♭ g s → M s (Val t) Σ
  getd d f h = return (getSlot d f h) f h

  getl : ∀ {s s' Σ} → s' ∈ edgesOf♭ g s → M s (Frame s') Σ
  getl e f h = return (getLink e f h) f h

  setd  :  ∀ {s t Σ} → t ∈ declsOf♭ g s → Val t Σ → M s (λ _ → ⊤) Σ
  setd d v f h with (setSlot d v f h)
  ...             | h' = return tt f h'

  setv  :  ∀ {s t Σ} → (g ⊢♭ s ↦ t) → Val t Σ → M s (λ _ → ⊤) Σ
  setv p v f h with (setVal p v f h)
  ...             | h' = return tt f h'
