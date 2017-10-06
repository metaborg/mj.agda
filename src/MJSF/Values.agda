open import Data.Nat
open import Data.List.Most
open import Data.Integer
open import Data.Product

-- This file contains the definition of values for the definitional
-- interpreter for MJ using scopes and frames, described in Section 5
-- of the paper.

module MJSF.Values (k : ℕ) where

open import MJSF.Syntax k
open import ScopesFrames.ScopesFrames k Ty

module ValuesG (g : Graph) where

  open SyntaxG g
  open UsesGraph g public
  open import Common.Weakening

  ------------
  -- VALUES --
  ------------

  -- The values used in our interpreter at run time are either:
  --
  -- * object references `ref`, represented in terms of a frame scoped
  --   by a class scope;
  --
  -- * null values (`ref` typed);
  --
  -- * an integer number literal (`int` typed); or
  --
  -- * `void` (`void typed -- note that there is no expression syntax
  --   for producing a `void` value directly, but method bodies still
  --   return `void`; we regard `void` as a unit type)

  data Val : VTy → List Scope → Set where
    ref    :  ∀ {s Σ} → Frame s Σ → Val (ref s) Σ
    null   :  ∀ {s Σ} → Val (ref s) Σ
    num    :  ∀ {Σ} → ℤ → Val int Σ
    void   :  ∀ {Σ} → Val void Σ

  -- There are three kinds of values stored in frame slots at run
  -- time, corresponding to each of the three kinds of declarations
  -- defined in `MJSF.Syntax`:
  --
  -- * values, as defined above;
  --
  -- * methods, where a method records a "self" frame `Frame s Σ` and
  --   a well-typed method definition `Meth s ts rt`, such that the
  --   scope of the method corresponds to the "self"; and
  --
  -- * classes which record a well-typed class definition and a
  --   witness that the class has a finite inheritance chain, both
  --   used for initializing new object instances, as well as a frame
  --   pointer to the root frame (class table).

  data Valᵗ : Ty → List Scope → Set where
    vᵗ : ∀ {t Σ} → Val t Σ → Valᵗ (vᵗ t) Σ
    mᵗ : ∀ {s ts rt Σ} → (self : Frame s Σ) → (body : Meth s ts rt) → Valᵗ (mᵗ ts rt) Σ
    cᵗ : ∀ {sʳ s s' Σ} → (class-def : Class sʳ s) → (ic : Inherits s s') → Frame sʳ Σ → Valᵗ (cᵗ sʳ s) Σ


  ---------------
  -- WEAKENING --
  ---------------

  -- We define notions of weakening for each of the values summarized above:

  val-weaken    :  ∀ {t Σ Σ'} → Σ ⊑ Σ' → Val t Σ → Val t Σ'
  val-weaken ext (num i)  =  num i
  val-weaken ext (ref f)  =  ref (wk ext f)
  val-weaken ext null     =  null
  val-weaken ext void     =  void

  instance
    val-weakenable : ∀ {t} → Weakenable (Val t)
    val-weakenable = record { wk = val-weaken }

  valᵗ-weaken : ∀ {t Σ Σ'} → Σ ⊑ Σ' → Valᵗ t Σ → Valᵗ t Σ'
  valᵗ-weaken ext (vᵗ v)      = vᵗ (val-weaken ext v)
  valᵗ-weaken ext (mᵗ f m)    = mᵗ (wk ext f) m
  valᵗ-weaken ext (cᵗ c ic f) = cᵗ c ic (wk ext f)

  -- And pass these to the scope graph definition:

  open UsesVal Valᵗ valᵗ-weaken renaming (getFrame to getFrame')

  
  --------------
  -- COERCION --
  --------------

  -- Our definition of sub-typing gives rise to a notion of sub-type
  -- coercion, defined below.  Coercions essentially traverse the
  -- inheritance links of the frame hierarchy for an object instance,
  -- as described in the paper.

  coerce<: : ∀ {t t' Σ} → t <: t' → Val t Σ → Heap Σ → Val t' Σ
  coerce<: refl v h = v
  coerce<: (super edge σ) null h = coerce<: σ null h
  coerce<: (super edge σ) (ref f) h
    with (lookup h f)
  ...  | (_ , links)  =  coerce<: σ (ref (lookup links edge)) h

