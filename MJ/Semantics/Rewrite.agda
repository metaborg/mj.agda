open import MJ.Types
open import MJ.Classtable

import MJ.Syntax as Syntax

module MJ.Semantics.Rewrite {c} (Σ : CT c) (ℂ : Syntax.Impl Σ) where

open import Prelude hiding (_⊔_)

open import Level using (_⊔_)
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

open import MJ.Semantics.Values Σ
open import MJ.Semantics.Objects.Flat Σ ℂ
open Membership-≡
open CT Σ
open Syntax Σ
open Heap encoding
open ObjEncoding encoding

data Redex (W : World c) : Ty c → Set where
  new  : ∀ cid → All (Val W) (Class.constr (clookup cid)) → Redex W (ref cid)
  iop  : NativeBinOp → (l r : Val W int) → Redex W int
  call : ∀ {cid as b} →
         Val W (ref cid) → Member Σ cid MTH (as , b) → All (Val W) as → Redex W b
  get  : ∀ {cid a} → Val W (ref cid) → Member Σ cid FLD a → Redex W a
  upcast : ∀ {c c'} → Σ ⊢ c <: c' → Val W (ref c) → Redex W (ref c')

mutual
  data ArgCtx {n}(Γ : Ctx c n)(W : World c)(i o y : Ty c) : List (Ty c) → Set where
    args : ∀ {xs ys} → All (Val W) xs → RedCtx Γ W i o → All (Expr Γ) ys →
            ArgCtx Γ W i o y (xs List.++ (y ∷ ys))

  data RedCtx {n}(Γ : Ctx c n)(W : World c) : Ty c → Ty c → Set where
    empty : ∀ {a} → RedCtx Γ W a a
    newₙ   : ∀ {a r} → (C : Fin c) →
             ArgCtx Γ W (ref C) r a (Class.constr (clookup C)) → RedCtx Γ W a r
    iop₁  : ∀ {r} → NativeBinOp → RedCtx Γ W int r → Expr Γ int → RedCtx Γ W int r
    iop₂  : ∀ {r} → NativeBinOp → Val W int → RedCtx Γ W int r → RedCtx Γ W int r
    call₁ : ∀ {r cid as b} → RedCtx Γ W b r → Member Σ cid MTH (as , b) →
            All (Expr Γ) as → RedCtx Γ W (ref cid) r
    call₂ : ∀ {cid as b a r} → Val W (ref cid) → Member Σ cid MTH (as , b) →
            ArgCtx Γ W b r a as → RedCtx Γ W a r
    get   : ∀ {cid a r} → RedCtx Γ W a r → Member Σ cid FLD a → RedCtx Γ W (ref cid) r
    upcast : ∀ {c c' r} → Σ ⊢ c <: c' → RedCtx Γ W (ref c') r → RedCtx Γ W (ref c) r


postulate init : ∀ {W} cid → Cont (fromList (Class.constr (clookup cid))) (λ W → Obj W cid) W

mutual


  {-# NON_TERMINATING #-}
  decompose : ∀ {n}{Γ : Ctx c n}{W a r} →
              Expr Γ a → RedCtx Γ W a r → Cont Γ (λ W → Val W r ⊎ ∃ λ b → Redex W b × RedCtx Γ W b r) W
  decompose unit k = decompose-aux k unit
  decompose (num x) k = decompose-aux k (num x)
  decompose (new C es) k with clookup C | inspect clookup C
  decompose (new C []) k | class parent [] decls | [ eq ] = decompose-aux k {!init!}
  decompose (new C (e ∷ es)) k | class parent (a ∷ as) decls | [ eq ] =
    decompose e
      (newₙ C (subst (λ C → ArgCtx _ _ _ _ _ (Class.constr C)) (sym eq) (args [] k es)))
  decompose (iop f l r) k = decompose l (iop₁ f k r)
  decompose (call e m es) k = decompose e (call₁ k m es)
  decompose (var i) k E μ = decompose-aux k (Vec∀.lookup i E) E μ
  decompose (get e x) k = decompose e (get k x)
  decompose (upcast x e) k = decompose e (upcast x k)

  decompose-args : ∀ {n}{Γ : Ctx c n}{W i o as} →
                  All (Expr Γ) as →
                  RedCtx Γ W i o → Cont Γ (λ W → Val W o ⊎ ∃ λ b → Redex W b × ArgCtx Γ W i o b as) W
  decompose-args [] k = {!!}
  decompose-args (e ∷ es) k with decompose e {!!}
  ... | z = {!!}

  {-# NON_TERMINATING #-}
  decompose-aux : ∀ {n}{Γ : Ctx c n}{W a r} →
                  RedCtx Γ W a r → Val W a → Cont Γ (λ W → Val W r ⊎ ∃ λ b → Redex W b × RedCtx Γ W b r) W
  decompose-aux empty v E μ = , ⊑-refl , μ , inj₁ v
  decompose-aux (newₙ C x) v = {!!}
  decompose-aux (iop₁ f k e) v = decompose e (iop₂ f v k)
  decompose-aux (iop₂ f v₁ k) v₂ E μ = , ⊑-refl , μ , inj₂ (, iop f v₁ v₂ , k)
  decompose-aux (call₁ k x x₁) v = {!!}
  decompose-aux (call₂ x x₁ x₂) v = {!!}
  decompose-aux (get k x) v = {!!}
  decompose-aux (upcast x k) v = {!!}

reduce : ∀ {n}{Γ : Ctx c n}{W a} → Expr Γ a → Cont Γ (λ W → Expr Γ a) W
reduce e = {!!}
