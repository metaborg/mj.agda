open import Data.Nat hiding (_^_)
open import Data.List.Most
open import Data.Product hiding (map)
open import Data.Unit
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

-- This file contains the definition of monads used for computation in
-- the definitional interpreter for MJ using scopes and frames,
-- described in Section 5 of the paper.

module MJSF.Monad (k : ℕ) where

open import MJSF.Syntax k
open import MJSF.Values k
open import ScopesFrames.ScopesFrames k Ty

module MonadG (g : Graph) where

  open SyntaxG g
  open ValuesG g
  open UsesVal Valᵗ valᵗ-weaken renaming (getFrame to getFrame')
  open import Common.Weakening

  -- Computations may either time out, raise a null-pointer exception,
  -- or successfully terminate to produce a result:

  data Res (a : Set) : Set where
    timeout : Res a
    nullpointer : Res a
    ok : (x : a) → Res a

  -- The monad is similar to the monad used for STLCSF, except it uses
  -- `Res` instead of `Maybe`:

  M : (s : Scope) → (List Scope → Set) → List Scope → Set
  M s p Σ = Frame s Σ → Heap Σ → Res (∃ λ Σ' → (Heap Σ' × p Σ' × Σ ⊑ Σ'))

  -- We define some usual monad operations:
  
  return     :  ∀ {s Σ}{p : List Scope → Set} → p Σ → M s p Σ
  return v f h = ok (_ , h , v , ⊑-refl)

  fmap : ∀ {A B : List Scope → Set}{Γ Σ} → (∀ {Σ} → A Σ → B Σ) → M Γ A Σ → M Γ B Σ
  fmap g m f h
    with (m f h)
  ...  | timeout = timeout
  ...  | nullpointer = nullpointer
  ...  | ok (Σ' , h' , v' , ext') = ok (Σ' , h' , g v' , ext')

  join : ∀ {A : List Scope → Set}{Γ Σ} → M Γ (M Γ A) Σ → M Γ A Σ
  join m f h
    with (m f h)
  ...  | timeout = timeout
  ...  | nullpointer = nullpointer
  ...  | ok (Σ' , h' , m' , ext')
       with (m' (wk ext' f) h')
  ...     | timeout = timeout
  ...     | nullpointer = nullpointer
  ...     | ok (Σ'' , h'' , v'' , ext'') = ok ((Σ'' , h'' , v'' , ext' ⊚ ext''))

  _>>=_     :  ∀ {s Σ}{p q : List Scope → Set} →
               M s p Σ → (∀ {Σ'} → p Σ' → M s q Σ') → M s q Σ
  (a >>= b) = join (fmap b a)

  -- To program in dependent-passing style, we use the variant of
  -- monadic strength also used for STLCSF.
  
  _^_  :  ∀ {Σ Γ}{p q : List Scope → Set} ⦃ w : Weakenable q ⦄ →
          M Γ p Σ → q Σ → M Γ (p ⊗ q) Σ
  (a ^ x) f h
    with (a f h)
  ...  | timeout = timeout
  ...  | nullpointer = nullpointer
  ...  | ok (Σ , h' , v , ext) = ok (Σ , h' , (v , wk ext x) , ext)

  -- The remaining definitions in this file are straightforward
  -- monadic liftings of the coercion function from `MJSF.Values` and
  -- of the frame operations.

  coerceᴹ :  ∀ {t t' s Σ} → t <: t' → M s (Val t) Σ → M s (Val t') Σ
  coerceᴹ σ m f h
    with (m f h)
  ...  | timeout = timeout
  ...  | nullpointer = nullpointer
  ...  | ok (Σ , h' , v , ext) = ok (Σ , h' , coerce<: σ v h' , ext)

  getFrame   :  ∀ {s Σ} → M s (Frame s) Σ
  getFrame f = return f f

  usingFrame  :  ∀ {s s' Σ}{p : List Scope → Set} → Frame s Σ → M s p Σ → M s' p Σ
  usingFrame f a _ = a f

  timeoutᴹ    :  ∀ {s Σ}{p : List Scope → Set} → M s p Σ
  timeoutᴹ _ _ = timeout

  raise : ∀ {s Σ}{p : List Scope → Set} → M s p Σ
  raise _ _ = nullpointer

  init : ∀ {Σ s' ds es} → (s : Scope) → ⦃ shape : g s ≡ (ds , es) ⦄ →
               Slots ds Σ → Links es Σ → M s' (Frame s) Σ
  init {Σ} s slots links _ h
    with (initFrame s slots links h)
  ...  | (f' , h') = ok (_ , h' , f' , ∷ʳ-⊒ s Σ)

  initι : ∀ {Σ s' ds es} → (s : Scope) → ⦃ shape : g s ≡ (ds , es) ⦄ →
               (Frame s (Σ ∷ʳ s) → Slots ds (Σ ∷ʳ s)) → Links es Σ → M s' (Frame s) Σ
  initι {Σ} s slots links _ h
    with (initFrameι s slots links h)
  ...  | (f' , h') = ok (_ , h' , f' , ∷ʳ-⊒ s Σ)

  getv : ∀ {s t Σ} → (s ↦ t) → M s (Valᵗ t) Σ
  getv p f h = return (getVal p f h) f h

  getf : ∀ {s s' Σ} → (s ⟶ s')  → M s (Frame s') Σ
  getf p f h = return (getFrame' p f h) f h

  getd : ∀ {s t Σ} → t ∈ declsOf s → M s (Valᵗ t) Σ
  getd d f h = return (getSlot d f h) f h

  getl : ∀ {s s' Σ} → s' ∈ edgesOf s → M s (Frame s') Σ
  getl e f h = return (getLink e f h) f h

  setd  :  ∀ {s t Σ} → t ∈ declsOf s → Valᵗ t Σ → M s (λ _ → ⊤) Σ
  setd d v f h with (setSlot d v f h)
  ...             | h' = return tt f h'

  setv  :  ∀ {s t Σ} → (s ↦ t) → Valᵗ t Σ → M s (λ _ → ⊤) Σ
  setv p v f h with (setVal p v f h)
  ...             | h' = return tt f h'
