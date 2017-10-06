open import Data.Nat
open import Data.Fin using (Fin; #_; suc; zero)
open import Data.List.Most
open import Data.Integer hiding (suc)
open import Data.Product hiding (map)
open import Data.Unit
open import Data.Star hiding (return ; _>>=_ ; map)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Data.Empty

-- This file contains the syntax for the definitional interpreter for
-- MJ using scopes and frames, described in Section 5 of the paper.

-- The definitions are parameterized by a scope graph of size `k`, as
-- usual:

module MJSF.Syntax (k : ℕ) where

private
  Scope : Set
  Scope = Fin k

-- Return types, method parameters, and field types in MJ are given by
-- `VTy`:

data VTy : Set where
  void : VTy
  int : VTy
  ref : Scope → VTy

-- The scope graph library is parameterized by a single kind of type,
-- to be used for all declarations.  But there are three different
-- kinds of names (declarations) in MJ: value declarations (e.g., for
-- fields and method parameters); method declarations; and class
-- declarations.
--
-- We use the following type to "tag" and distinguish the various
-- kinds of declarations.

data Ty : Set where
  vᵗ : VTy → Ty
  mᵗ : List VTy → VTy → Ty
  cᵗ : Scope → Scope → Ty

-- We specialize the scopes-and-frames library to the size of our
-- scope graph, and the tagged type for declarations above:

open import ScopesFrames.ScopesFrames k Ty hiding (Scope)


-------------
-- HAS TAG --
-------------

-- As summarized above, declarations may be either value-typed,
-- method-typed, or class-typed.  We introduce some parameterized
-- predicates which only hold for a particular tag.  This is useful
-- for saying that some list of types `ts : List Ty` only contains
-- value types, and that a particular property holds for each of those
-- value types.  For example, the type `All (#v (λ _ → ⊤)) ts`
-- guarantees that `ts` contains only value types, and does not
-- constrain the value types further (due to the use of `⊤`).

data #v : (VTy → Set) → Ty → Set where
  #v' : ∀ {t p} → p t → #v p (vᵗ t)

data #m : (List VTy → VTy → Set) → Ty → Set where
  #m' : ∀ {ts rt p} → p ts rt → #m p (mᵗ ts rt)

data #c (sʳ : Scope) (p : Scope → Set) : Ty → Set where
  #c' : ∀ {s} → p s → #c sʳ p (cᵗ sʳ s)


module SyntaxG (g : Graph) where

  open UsesGraph g


  -------------------------------
  -- SUBTYPING AND INHERITANCE --
  -------------------------------

  -- As summarized in the paper, we define sub-typing in terms of
  -- inheritance edges between class scopes in the scope graph:

  data _<:_ : VTy → VTy → Set where
    refl   :  ∀ {t} → t <: t
    super  :  ∀ {s1 s2 t} →
              s2 ∈ edgesOf s1 → (ref s2) <: t → (ref s1) <: t

  -- Scope graphs may be cyclic, and there is (in theory) nothing that
  -- prevents classes from mutually extending one another, thereby
  -- creating cyclic inheritance chains.  The following `Inherits`
  -- type witnesses that a given class scope has a finite set of
  -- inheritance steps.  This property is useful for defining object
  -- initialization in a way that lets Agda prove that object
  -- initialization takes finite time (i.e., no need for fuel).

  data Inherits : Scope → Scope → Set where
    obj   : ∀ s {ds sʳ} ⦃ shape : g s ≡ (ds , [ sʳ ]) ⦄ → Inherits s s
    super : ∀ {s ds sʳ sᵖ s'} ⦃ shape : g s ≡ (ds , sʳ ∷ sᵖ ∷ []) ⦄ → Inherits sᵖ s' → Inherits s s'


  ------------
  -- SYNTAX --
  ------------

  -- The expressions of MJ where the `s` in `Expr s t` is the lexical
  -- context scope:

  data Expr (s : Scope) : VTy → Set where
    call     :  ∀ {s' ts t} → Expr s (ref s') → -- receiver
                (s' ↦ (mᵗ ts t)) →              -- path to method declaration
                All (Expr s) ts →               -- argument list
                Expr s t
    get      :  ∀ {s' t} → Expr s (ref s') → (s' ↦ vᵗ t) → Expr s t
    var      :  ∀ {t} → (s ↦ vᵗ t) → Expr s t
    new      :  ∀ {sʳ s'} → s ↦ cᵗ sʳ s' → Expr s (ref s') -- path to class declaration
    null     :  ∀ {s'} → Expr s (ref s')
    num      :  ℤ → Expr s int
    iop      :  (ℤ → ℤ → ℤ) → (l r : Expr s int) → Expr s int
    upcast   :  ∀ {t' t} → t' <: t → Expr s t' → Expr s t
    this     :  ∀ {s' self} → s ⟶ s' → self ∈ edgesOf s' → -- the `self` of objects is given by the lexical parent edge of a method
                Expr s (ref self)

  -- The statements of MJ where the `s` in `Stmt s t s'` is the
  -- lexical context scope before the statement `t` is the return type
  -- of the statement, and `s'` is the leixcal context scope after the
  -- statement.

  mutual
    data Stmt (s : Scope)(r : VTy) : Scope → Set where
      do    : ∀ {t'} → Expr s t' → Stmt s r s
      ifz   : ∀ {s' s'' : Scope} → Expr s int → Stmt s r s → Stmt s r s → Stmt s r s -- branches are blocks
      set   : ∀ {s' t'} → Expr s (ref s') → (s' ↦ vᵗ t') → Expr s t' → Stmt s r s
      loc   : ∀ (s' : Scope)(t' : VTy)⦃ shape : g s' ≡ ([ vᵗ t' ] , [ s ]) ⦄ → Stmt s r s' -- local variable scope `s'` is connected to lexical context scope `s`
      asgn  : ∀ {t'} → (s ↦ vᵗ t') → Expr s t' → Stmt s r s
      ret   : Expr s r → Stmt s r s
      block : ∀ {s'} → Stmts s r s' → Stmt s r s

    -- A block of statements is given by a sequence of statements
    -- whose scopes are lexically nested (if at all):

    Stmts : Scope → VTy → Scope → Set
    Stmts s r s' = Star (λ s s' → Stmt s r s') s s'

  -- Method bodies have a mandatory return expression, except for
  -- `void` typed method bodies:

  data Body (s : Scope) : VTy → Set where
    body      : ∀ {s' t} → Stmts s t s' → Expr s' t → Body s t
    body-void : ∀ {s'} → Stmts s void s' → Body s void

  -- A method defines the scope shape mandating that the method type
  -- parameters are declarations of the method body scope, and that
  -- the method body scope is connected to the scope of the class
  -- where they are defined.  The `s` in `Meth s ts t` is the scope of
  -- the surrounding class.

  data Meth (s : Scope) : List VTy → VTy → Set where
    meth  :  ∀ {ts rt}(s' : Scope)
             ⦃ shape : g s' ≡ (map vᵗ ts , [ s ]) ⦄ →
             Body s' rt →
             Meth s ts rt

  -- A class definition has an optional path to a super class; the
  -- only difference between a `class0` and a `class1` is that a
  -- `class1` has a path from the root scope `sʳ` to another class
  -- declaration, i.e., the super class.
  --
  -- The `sʳ` in `Class sʳ s` is the root scope (representing the
  -- class table), and the `s` is the scope of the defined class.
  --
  -- We distinguish three kinds of class members in MJ:
  --
  -- * Fields, typed by `fs`.
  --
  -- * Methods, typed by `ms`, where for each method type signature
  --   `mᵗ ts t` in `ms` there is a well-typed method `Meth s ts t`.
  --
  -- * Overriding methods, typed by `oms`, where for each method type
  --   signature `mᵗ ts t` in `oms` there is a path from the current
  --   class scope to a method declaration in a parent class scope,
  --   and a well-typed method `Meth s ts t` which overrides the
  --   method corresponding to that declaration.

  data Class (sʳ s : Scope) : Set where
    class1  :  ∀ {ms fs oms sᵖ} →
               sʳ ↦ (cᵗ sʳ sᵖ) →
               ⦃ shape  :  g s  ≡  (ms ++ fs ,  sʳ ∷ sᵖ ∷ []) ⦄ →
               All (#m (Meth s)) ms →
               All (#v (λ _ → ⊤)) fs →
               All (#m (λ ts rt → (s ↦ (mᵗ ts rt)) × Meth s ts rt )) oms → -- overrides
               Class sʳ s
    class0 : ∀ {ms fs oms} →
             ⦃ shape : g s ≡ (ms ++ fs , [ sʳ ]) ⦄ →
             All (#m (Meth s)) ms →   -- only methods
             All (#v (λ _ → ⊤)) fs →  -- only values
             All (#m (λ ts rt → (s ↦ (mᵗ ts rt)) × Meth s ts rt )) oms → -- overrides
             Class sʳ s

  -- A program consists of a sequence of well-typed class definitions
  -- and a main function to be evaluated in the context of the root
  -- scope.  The root scope has only class-typed declarations, and has
  -- no parent edges:

  data Program (sʳ : Scope)(a : VTy) : Set where
    program :
      ∀ cs ⦃ shape : g sʳ ≡ (cs , []) ⦄ →
        -- implementation of all the classes
        All (#c sʳ (λ s → Class sʳ s × ∃ λ s' → Inherits s s')) cs →
        -- main function
        Body sʳ a →
        Program sʳ a
