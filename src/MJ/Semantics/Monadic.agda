import MJ.Classtable

import MJ.Syntax as Syntax
import MJ.Semantics.Values as Values
import MJ.Classtable.Core as Core
import MJ.Classtable.Code as Code

--
-- Substitution-free interpretation of welltyped MJ
--

module MJ.Semantics.Monadic
  {c}(Ct : Core.Classtable c)(ℂ : Code.Code Ct) where

open import Level renaming (zero to ℓz; suc to ℓs)
open import Prelude hiding (_^_; _+_)
open import Data.Vec hiding (init; _>>=_; _∈_)
open import Data.Vec.All.Properties.Extra as Vec∀++
open import Data.List.Most as List
open import Relation.Nullary.Decidable
open import Data.Star hiding (return; _>>=_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Integer as Int hiding (suc; -_)
import Data.Bool as Bool
open import Data.Unit

open Values Ct renaming (Val to Val')
open Syntax Ct
open Code Ct
open Core c
open Classtable Ct

open import MJ.Syntax.BinOp Ct
open import MJ.Syntax.Program Ct
open import MJ.Classtable.Membership Ct
open import MJ.Types
open import MJ.LexicalScope c
open import MJ.Semantics.Environments Ct
open import MJ.Semantics.BinOp Ct
open import MJ.Semantics.Objects Ct
open import MJ.Semantics.Objects.Flat Ct using (encoding)
open import Common.Weakening

open ObjEncoding encoding renaming (StoreVal to StoreVal')

private
  pre = ⊑-preorder {A = Ty⁺ c}
  Val = flip Val'
  StoreVal = flip StoreVal'

open import Relation.Unary hiding (_∈_)
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Unary.Monotone pre
open import Relation.Unary.Monotone.Prefix
open import Category.Monad.Monotone pre
open import Category.Monad.Monotone.Reader pre
open import Category.Monad.Monotone.State pre
open import Category.Monad.Monotone.Error pre
open import Category.Monad.Monotone.Heap pre (Ty⁺ c) StoreVal Store _∈_

module Monadic
  (M : Pred (World c) ℓz → Pt (World c) ℓz)
  (MM : ∀ E ⦃ mono-E : Monotone E ⦄ → RawMPMonad (M E))
  (MR : ∀ E ⦃ mono-E : Monotone E ⦄ → ReaderMonad E M)
  (MS : ∀ E ⦃ mono-E : Monotone E ⦄ → HeapMonad (M E))
  (MT : ∀ E ⦃ mono-E : Monotone E ⦄ → ErrorMonad ⊤ (M E))
  (ME : ∀ E ⦃ mono-E : Monotone E ⦄ → ErrorMonad Exception (M E))
  where

  module _ {E}⦃ E-mono : Monotone E ⦄ where
    open RawMPMonad (MM E) public
    open ErrorMonad ⊤ (MT E) using () renaming (throw to timeout) public
    open ErrorMonad Exception (ME E) public renaming (try_catch_ to do-try_catch_)
    open ReaderMonad (MR E) public
    open HeapMonad (MS E) public hiding (super)

  {-
  Lifting of object getter/setter into the monad
  -}
  read-field : ∀ {Γ : Ctx}{C f a} → IsMember C FIELD f a → Val (ref C) ⊆ M (Env Γ) (Val a)
  read-field m null = throw nullderef
  read-field m (ref o C<:C') = do
    obj cid O ← deref o
    return (getter _ O (inherit' C<:C' m))

  write-field : ∀ {Γ C f a} → IsMember C FIELD f a → Val (ref C) ⊆ (Val a ⇒ M (Env Γ) (Val (ref C)))
  write-field m null v = throw nullderef
  write-field m (ref o s) v = do
    (obj cid O , o) , v ← deref o ^ o ^ v
    let vobj            = obj cid (setter _ O (inherit' s m) v)
    _ , o               ← modify o (vobj) ^ o
    return (ref o s)

  continue : ∀ {E W a} ⦃ mono-E : Monotone E ⦄ → M E (Val a ∪ E) W
  continue = asks inj₂

  mutual

    {-
    Arguments are passed as mutable and thus have to be evaluated, after which
    we store the values in the store and we pass the references.
    -}
    eval-args : ∀ {Γ as W} → ℕ → All (Expr Γ) as → M (Env Γ) (λ W' → All (λ a → vty a ∈ W') as) W
    eval-args k args = sequenceM (map-all (λ e {_} _ → eval-arg k e) args)
      where
        eval-arg : ∀ {Γ a} → ℕ → Expr Γ a → ∀ {W} → M (Env Γ) (_∈_ (vty a)) W
        eval-arg k e = do
          v ← evalₑ k e
          store (val v)

    {-
    Object initialization:
    Creates a default object; stores a mutable reference to it on the heap; calls the constructor
    on the resulting reference.
    -}
    constructM : ℕ → ∀ cid {W} → M (Env (Class.constr (Σ cid))) (Val (ref cid)) W
    constructM k cid = do
      r      ← store (obj _ (defaultObject cid))
      r' , r ← store (val (ref r ε)) ^ r
      let (implementation construct mbodies) = ℂ cid
      _  , r ← local (λ E → r' ∷ E) (eval-constructor k ε r construct) ^ r
      return (ref r ε)

    {-
    Constructor interpretation:
    The difficult case being the one where we have a super call.
    -}
    eval-constructor : ∀ {cid' cid W} → ℕ → Σ ⊢ cid' <: cid → (obj cid') ∈ W → Constructor cid →
                       M (Env (constrctx cid)) (Val void) W
    eval-constructor zero _ _ _ = timeout tt
    eval-constructor {_}{Object} (suc k) _ _ _ = return unit
    eval-constructor {_}{cls cid} (suc k) s o∈W (super args then b) = do
      let s'        = s ◅◅ super ◅ ε
      let pid       = Class.parent (Σ (cls cid))
      let super-con = Implementation.construct (ℂ pid)
      -- eval the super arguments
      rvs , o∈W       ← eval-args k args ^ o∈W
      -- store a parent pointer for passing to super
      sup , o∈W , rvs ← store (val (ref o∈W s')) ^ (o∈W , rvs)
      _               ← local (λ _ → sup ∷ rvs) (eval-constructor k s' o∈W super-con)
      -- evaluate own body
      _               ← eval-body k b
      return unit

    eval-constructor {_}{cls id} (suc k) _ _ (body x) = do
      _ ← eval-body k x
      return unit

    {-
    Method evaluation including super calls.
    The difficult case again being the one where we have a super call.
    -}
    eval-method : ∀ {cid m as b pid W E}⦃ mono-E : Monotone E ⦄ → ℕ →
                  Σ ⊢ cid <: pid → (obj cid) ∈ W →
                  All (λ ty → vty ty ∈ W) as →
                  InheritedMethod pid m (as , b) → M E (Val b) W

    eval-method zero _ _ _ _ = timeout _

    eval-method (suc k) s o args (pid' , pid<:pid' , body b) = do
      mutself , args ← store (val (ref o (s ◅◅ pid<:pid'))) ^ args
      local (λ E → mutself ∷ args) (eval-body k b)

    -- calling a method on Object is improbable...
    eval-method {_}{m}{as}{b} (suc k) s o args (Object , _ , super x ⟨ _ ⟩then _) =
      ⊥-elim (∉Object (subst (λ O → IsMember O _ _ _) founded (sound x)))

    eval-method {E = E} (suc k) s o args (cls pid' , pid<:pid' , super x ⟨ supargs ⟩then b) = do
        let super-met = method ℂ (Class.parent (Σ (cls pid'))) (sound x)
        -- store a cast this-reference
        mutself , args , o       ← ts _ ⦃ mono-∩ ⦄ (store (val (ref o (s ◅◅ pid<:pid')))) (args , o)
        -- eval super args in method context
        rvs , args , o           ← local (λ _ → mutself ∷ args) (eval-args k supargs) ^ (args , o)
        -- call super
        retv , args , o          ← eval-method k (s ◅◅ pid<:pid' ◅◅ super ◅ ε) o rvs super-met ^ (args , o)
        -- store the super return value to be used as a mutable local
        mutret , args , o        ← store (val retv) ^ (args , o)
        -- store the cast this-reference
        mutself' , mutret , args ← store (val (ref o (s ◅◅ pid<:pid'))) ^ (mutret , args)
        -- call body
        local (λ _ → mutret ∷ mutself' ∷ args) (eval-body k b)

    {-
    evaluation of expressions
    -}
    evalₑ : ∀ {Γ : Ctx}{a} → ℕ → Expr Γ a → ∀ {W} → M (Env Γ) (Val a) W
    evalₑ zero _ = timeout _

    -- primitive values
    evalₑ (suc k) unit =
      return unit

    evalₑ (suc k) (num n) =
      return (num n)

    evalₑ (suc k) (bool b) =
      return (bool b)

    evalₑ (suc k) null =
      return null

    -- variable lookup
    evalₑ (suc k) (var x) = do
      v     ← asks (λ E → ∈-all x E)
      val w ← deref v
      return w

    evalₑ (suc k) (upcast ε e) = evalₑ k e
    evalₑ (suc k) (upcast s₁@(_ ◅ _) e) = do
      (ref o s₂ ) ← evalₑ k e where null → return null
      return $ ref o (s₂ ◅◅ s₁)

    -- binary interger operations
    evalₑ (suc k) (bop f l r) = do
      vₗ      ← evalₑ k l
      vᵣ , vₗ  ← evalₑ k r ^ vₗ
      return (eval-bop f vₗ vᵣ)

    -- method calls
    evalₑ (suc k) (call e _ {acc = mtd} args) = do
      ref {dyn-cid} o s₁ ← evalₑ k e where null → throw nullderef
      -- evaluate the arguments
      rvs , o            ← eval-args k args ^ o
      -- dynamic dispatch: dynamic lookup of the method on the runtime class of the reference
      -- and execution of the call
      (eval-method k ε o rvs (method ℂ dyn-cid (sound (inherit _ s₁ mtd))))

    -- field lookup in the heap
    evalₑ (suc k) (get e _ {_}{fld}) = do
      ref o s ← evalₑ k e where null → throw nullderef
      obj c O ← deref o
      return (getter _ O $ inherit' s (sound fld))

    -- object allocation
    evalₑ (suc k) (new C args) = do
      rvs ← eval-args k args
      local (λ _ → rvs) (constructM k C)

    {-
    Statement evaluation
    -}
    evalc : ∀ {I : Ctx}{O : Ctx}{W : World c}{a} → ℕ →
            Stmt I a O → M (Env I) (λ W → Val a W ⊎ Env O W) W

    evalc zero _ = timeout _

    evalc (suc k) raise = throw other

    evalc (suc k) (block stmts) = do
      (right _) ← eval-stmts k stmts
        where (left v) → return (left v)
      continue

    evalc (suc k) (try cs catch cs') =
      do-try
        (do
          (right _) ← evalc k cs
            where (left v) → return (left v)
          continue
        )
      catch
        (λ _ e → do
          _ ← evalc k cs'
          continue
        )

    -- new local variable
    evalc (suc k) (loc a) = do
      r ← store (val $ default a)
      asks λ E → inj₂ (r ∷ E)

    -- assigning to a local
    evalc (suc k) (asgn x e) = do
      v        ← evalₑ k e
      addr , v ← asks (λ E → ∈-all x E) ^ v
      _        ← modify addr (val v)
      continue

    -- setting a field
    evalc (suc k) (set r _ {_}{fld} e) = do
      r'@(ref _ _) ← evalₑ k r where null → throw nullderef
      (v , r')     ← evalₑ k e ^ r'
      _            ← write-field (sound fld) r' v
      continue

    -- side-effectful expressions
    evalc (suc k) (run e) = do
      _ ← evalₑ k e
      continue

    -- early returns
    evalc (suc k) (ret e) = do
      v ← evalₑ k e
      return (inj₁ v)

    -- if-then-else blocks
    evalc (suc k) (if e then cs else ds) = do
      bool b ← evalₑ k e
      Bool.if b
        then evalc k cs
        else evalc k ds

    -- while loops
    evalc (suc k) (while e run b) = do
      bool v ← evalₑ (suc k) e
      Bool.if v
        then (do
          _ ← evalc k b
          evalc k (while e run b)
        )
        else continue

    {-
    An helper for interpreting a sequence of statements
    -}
    eval-stmts : ∀ {Γ Γ' W a} → ℕ → Stmts Γ a Γ' → M (Env Γ) (Val a ∪ Env Γ') W
    eval-stmts k ε = continue
    eval-stmts k (x ◅ st) = do
      (right E') ← evalc k x
        where (left v) → return (left v)
      local (λ _ → E') (eval-stmts k st)

    {-
    An helper for interpreting method bodies (i.e. sequence of Stmts optionally followed by a return).
    -}
    eval-body : ∀ {I : Ctx}{W : World c}{a} → ℕ → Body I a → M (Env I) (Val a) W
    eval-body k (body ε re) = evalₑ k re
    eval-body k (body stmts@(_ ◅ _) e) = do
      (right E) ← eval-stmts k stmts
         where (left v) → return v
      local (λ _ → E) (evalₑ k e)
