open import MJ.Types
open import MJ.Classtable

import MJ.Syntax as Syntax
import MJ.Semantics.Values as Values

--
-- Substitution-free interpretation of welltyped MJ
--

module MJ.Semantics.Functional {c} (Σ : CT c) (ℂ : Syntax.Impl Σ) where

open import Prelude

open import Data.Vec hiding (init)
open import Data.Vec.All.Properties.Extra as Vec∀++
open import Data.Sum
open import Data.List as List
open import Data.List.All as List∀ hiding (lookup)
open import Data.List.All.Properties.Extra
open import Data.List.Any
open import Data.List.Prefix
open import Data.List.Properties.Extra as List+
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
open import Data.Star.Indexed

import Data.Vec.All as Vec∀

open Membership-≡
open Values Σ
open CT Σ
open Syntax Σ

-- open import MJ.Semantics.Objects.Hierarchical Σ ℂ using (encoding)
open import MJ.Semantics.Objects.Flat Σ ℂ using (encoding)
open ObjEncoding encoding
open Heap encoding


⊒-res : ∀ {a}{I : World c → Set a}{W W'} → W' ⊒ W → Res I W' → Res I W
⊒-res {W = W} p (W' , ext' , μ' , v) = W' , ⊑-trans p ext' , μ' , v

mutual

  --
  -- object initialization
  --

  init : ∀ {W} cid → Cont (fromList (Class.constr (clookup cid))) (λ W → Obj W cid) W
  init cid E μ with Impl.bodies ℂ cid
  init cid E μ | impl super-args defs with evalₙ (defs FLD) E μ
  ... | W₁ , ext₁ , μ₁ , vs with clookup cid | inspect clookup cid

  -- case *without* super initialization
  init cid E μ | impl nothing defs | (W₁ , ext₁ , μ₁ , vs) | (class nothing constr decls) | [ eq ] =
    W₁ , ext₁ , μ₁ , vs

  -- case *with* super initialization
  init cid E μ | impl (just sc) defs | (W₁ , ext₁ , μ₁ , vs) |
    (class (just x) constr decls) | [ eq ] with evalₑ-all sc (Vec∀.map (coerce ext₁) E) μ₁
  ... | W₂ , ext₂ , μ₂ , svs with init x (all-fromList svs) μ₂
  ... | W₃ , ext₃ , μ₃ , inherited = W₃ , ⊑-trans (⊑-trans ext₁ ext₂) ext₃ , μ₃ ,
    (List∀.map (coerce (⊑-trans ext₂ ext₃)) vs ++-all inherited)

  {-}
  init cid E μ with Impl.bodies ℂ cid
  init cid E μ | impl super-args defs with evalₙ (defs FLD) E μ
  ... | W₁ , ext₁ , μ₁ , vs with clookup cid | inspect clookup cid

  -- case *without* super initialization
  init cid E μ | impl nothing defs | (W₁ , ext₁ , μ₁ , vs) |
    (class nothing constr decls) | [ eq ] =
    , ext₁
    , μ₁
    , record {
      own = λ{
        MTH → List∀.tabulate (λ _ → tt) ;
        FLD → subst (λ C → All _ (Class.decls C FLD)) (sym eq) vs
      };
      inherited = subst (λ C → Maybe.All _ (Class.parent C)) (sym eq) nothing
    }

  -- case *with* super initialization
  init cid E μ | impl (just sc) defs | (W₁ , ext₁ , μ₁ , vs) |
    (class (just x) constr decls) | [ eq ] with evalₑ-all sc (Vec∀.map (coerce ext₁) E) μ₁
  ... | W₂ , ext₂ , μ₂ , svs with init x (all-fromList svs) μ₂
  ... | W₃ , ext₃ , μ₃ , sO =
    , ⊑-trans (⊑-trans ext₁ ext₂) ext₃
    , μ₃
    , record {
      own = λ{
        MTH → List∀.tabulate (λ _ → tt) ;
        FLD → subst
          (λ C → All _ (Class.decls C FLD))
          (sym eq)
          (List∀.map (coerce (⊑-trans ext₂ ext₃)) vs)
      };
      inherited = subst (λ C → Maybe.All _ (Class.parent C)) (sym eq) (just sO)
    }
  -}

  evalₑ-all : ∀ {n}{Γ : Ctx c n}{as} →
              All (Expr Γ) as → ∀ {W} → Cont Γ (λ W' → All (Val W') as) W
  evalₑ-all [] E μ = , ⊑-refl , μ , []
  evalₑ-all (px ∷ exps) E μ with evalₑ px E μ
  ... | W' , ext' , μ' , v with evalₑ-all exps (Vec∀.map (coerce ext') E) μ'
  ... | W'' , ext'' , μ'' , vs = W'' , ⊑-trans ext' ext'' , μ'' , coerce ext'' v ∷ vs

  --
  -- evaluation of expressions
  --

  {-# TERMINATING #-}
  evalₑ : ∀ {n}{Γ : Ctx c n}{a} → Expr Γ a → ∀ {W} → Cont Γ (flip Val a) W
  evalₑ (upcast sub e) E μ with evalₑ e E μ
  ... | W' , ext' , μ' , (ref r s) = W' , ext' , μ' , ref r (<:-trans s sub)

  -- primitive values
  evalₑ unit = pure (const unit)
  evalₑ (num n) = pure (const (num n))

  -- variable lookup
  evalₑ (var i) = pure (λ E → Vec∀.lookup i E)

  -- object allocation
  evalₑ (new C args) {W} E μ with evalₑ-all args E μ
  -- create the object, typed under the current heap shape
  ... | W₁ , ext₁ , μ₁ , vs with init C (all-fromList vs) μ₁
  ... | W₂ , ext₂ , μ₂ , O =
    let
      -- extension fact for the heap extended with the new object allocation
      ext = ∷ʳ-⊒ (obj C) W₂
    in
      , ⊑-trans (⊑-trans ext₁ ext₂) ext
      , all-∷ʳ (List∀.map (coerce ext) μ₂) (coerce ext (obj C O))
      , ref (∈-∷ʳ W₂ (obj C)) refl -- value typed under the extended heap

  -- binary interger operations
  evalₑ (iop f l r) E μ with evalₑ l E μ
  ... | W₁ , ext₁ , μ₁ , (num i) with evalₑ r (Vec∀.map (coerce ext₁) E) μ₁
  ... | W₂ , ext₂ , μ₂ , (num j) = W₂ , ⊑-trans ext₁ ext₂ , μ₂ , num (f i j)

  -- method calls
  evalₑ (call {C} e mtd args) E μ with evalₑ e E μ              -- eval obj expression
  ... | W₁ , ext₁ , μ₁ , r@(ref o sub) with ∈-all o μ₁         -- lookup obj on the heap
  ... | val ()
  ... | obj cid O with evalₑ-all args (Vec∀.map (coerce ext₁) E) μ₁ -- eval arguments
  ... | W₂ , ext₂ , μ₂ , vs =
    -- and finally eval the body of the method under the environment
    -- generated from the call arguments and the object's "this"
    ⊒-res
      (⊑-trans ext₁ ext₂)
      (eval-body cmd (ref (∈-⊒ o ext₂) <:-fact Vec∀.∷ all-fromList vs) μ₂)
    where
      -- get the method definition
      cmd = getDef C mtd ℂ
      -- get a subtyping fact
      <:-fact = <:-trans sub (proj₁ (proj₂ mtd))

  -- field lookup in the heap
  evalₑ (get e fld) E μ with evalₑ e E μ
  ... | W' , ext' , μ' , ref o C<:C₁ with ∈-all o μ'
  ... | (val ())
  -- apply the runtime subtyping fact to weaken the member fact
  ... | obj cid O = W' , ext' , μ' , getter O (mem-inherit Σ C<:C₁ fld)

  --
  -- command evaluation
  --

  evalc : ∀ {n m}{I : Ctx c n}{O : Ctx c m}{W : World c}{a} →
          -- we use a sum for abrupt returns
          Cmd I a O → Cont I (λ W → (Val W a) ⊎ (Env O W)) W

  -- new locals variable
  evalc (loc x e) E μ with evalₑ e E μ
  ... | W₁ , ext₁ , μ₁ , v = W₁ , ext₁ , μ₁ , inj₂ (v Vec∀.∷ (Vec∀.map (coerce ext₁) E))

  -- assigning to a local
  evalc (asgn i x) E μ with evalₑ x E μ
  ... | W₁ , ext₁ , μ₁ , v = W₁ , ext₁ , μ₁ , inj₂ (Vec∀.map (coerce ext₁) E Vec∀++.[ i ]≔ v)

  -- setting a field
  -- start by lookuping up the referenced object on the heap & eval the expression to assign it
  evalc (set rf fld e) E μ with evalₑ rf E μ
  ... | W₁ , ext₁ , μ₁ , ref p s with List∀.lookup μ₁ p | evalₑ e (Vec∀.map (coerce ext₁) E) μ₁
  ... | (val ()) | _
  ... | (obj cid O) | (W₂ , ext₂ , μ₂ , v) = let ext = ⊑-trans ext₁ ext₂ in
    , ext
    , (μ₂ All[ ∈-⊒ p ext₂ ]≔' -- update the store at the reference location
        -- update the object at the member location
        obj cid (
          setter (coerce ext₂ O) (mem-inherit Σ s fld) v
        )
      )
    , (inj₂ $ Vec∀.map (coerce ext) E)

  -- side-effectful expressions
  evalc (do x) E μ with evalₑ x E μ
  ... | W₁ , ext₁ , μ₁ , _ = W₁ , ext₁ , μ₁ , inj₂ (Vec∀.map (coerce ext₁) E)

  -- early returns
  evalc (ret x) E μ with evalₑ x E μ
  ... | W₁ , ext₁ , μ₁ , v = W₁ , ext₁ , μ₁ , inj₁ v

  eval-body : ∀ {n}{I : Ctx c n}{W : World c}{a} → Body I a → Cont I (λ W → Val W a) W
  eval-body (body ε re) E μ = evalₑ re E μ
  eval-body (body (x ◅ xs) re) E μ with evalc x E μ
  ... | W₁ , ext₁ , μ₁ , inj₂ E₁ = ⊒-res ext₁ (eval-body (body xs re) E₁ μ₁)
  ... | W₁ , ext₁ , μ₁ , inj₁ v = _ , ext₁ , μ₁ , v

  evalₙ : ∀ {n}{I : Ctx c n}{W : World c}{as} → All (Body I) as →
          Cont I (λ W → All (Val W) as) W
  evalₙ [] E μ = , ⊑-refl , μ , []
  evalₙ (px ∷ bs) E μ with eval-body px E μ
  ... | W₁ , ext₁ , μ₁ , v with evalₙ bs (Vec∀.map (coerce ext₁) E) μ₁
  ... | W₂ , ext₂ , μ₂ , vs = W₂ , ⊑-trans ext₁ ext₂ , μ₂ , coerce ext₂ v ∷ vs

  eval : ∀ {a} → Prog a → ∃ λ W → Store W × Val W a
  eval (lib , main) with eval-body main Vec∀.[] []
  ... | W , ext , μ , v = W , μ , v
