------------------------------------------------------------------------
-- Well-typed substitutions
-- From 
------------------------------------------------------------------------

module Extensions.Fin.TypedSubstitution where

import Category.Applicative.Indexed as Applicative
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Vec as Vec using (Vec; []; _∷_; map)
open import Data.Vec.All using (All₂; []; _∷_; map₂; gmap₂; gmap₂₁; gmap₂₂)
open import Data.Vec.Properties using (lookup-morphism)
open import Function using (_∘_; flip)
open import Relation.Binary.PropositionalEquality as PropEq hiding (trans)
open PropEq.≡-Reasoning


------------------------------------------------------------------------
-- Abstract typing contexts and well-typedness relations

-- Abstract typing contexts over T-types.
--
-- A typing context Ctx n maps n free variables to types containing up
-- to n free variables each.
module Context where

  infixr 5 _∷_

  -- Typing contexts.
  data Ctx (T : ℕ → Set) : ℕ → Set where
    []  :                               Ctx T 0
    _∷_ : ∀ {n} → T (1 + n) → Ctx T n → Ctx T (1 + n)

  -- Operations on context that require weakening of types.
  record WeakenOps (T : ℕ → Set) : Set where

    -- Weakening of types.
    field weaken : ∀ {n} → T n → T (1 + n)

    infixr 5 _i∷_

    -- Convert a context to its vector representation.
    toVec : ∀ {n} → Ctx T n → Vec (T n) n
    toVec []      = []
    toVec (a ∷ Γ) = a ∷ map weaken (toVec Γ)

    -- Shorthand for extending contexts with variables that are typed
    -- independently of themselves.
    _i∷_ : ∀ {n} → T n → Ctx T n → Ctx T (1 + n)
    a i∷ Γ = weaken a ∷ Γ

    -- Lookup the type of a variable in a context.
    lookup : ∀ {n} → Fin n → Ctx T n → T n
    lookup x = Vec.lookup x ∘ toVec

open Context

-- Abstract typings.
--
-- An abtract typing _⊢_∈_ : Typing Tp₁ Tm Tp₂ is a ternary relation
-- which, in a given Tp₂-context, relates Tm-terms to their Tp₁-types.
Typing : (ℕ → Set) → (ℕ → Set) → (ℕ → Set) → Set₁
Typing Tp₁ Tm Tp₂ = ∀ {n} → Ctx Tp₁ n → Tm n → Tp₂ n → Set


------------------------------------------------------------------------
-- Abstract well-typed substitutions (i.e. substitution lemmas)

-- Abstract typed substitutions.
record TypedSub (Tp₁ Tp₂ Tm : ℕ → Set) : Set₁ where

  infix 4 _⊢_∈_

  field
    _⊢_∈_ : Typing Tp₂ Tm Tp₁   -- the associated typing

    -- Application of Tm-substitutions to (source) Tp₁-types
    application : Application Tp₁ Tm

    -- Operations on the (source) Tp₁-context.
    weakenOps : WeakenOps Tp₁

  open Application application   public using (_/_)
  open WeakenOps   weakenOps            using (toVec)

  infix 4 _⇒_⊢_

  -- Typed substitutions.
  --
  -- A typed substitution Γ ⇒ Δ ⊢ σ is a substitution σ which, when
  -- applied to something that is well-typed in a source context Γ,
  -- yields something well-typed in a target context Δ.
  _⇒_⊢_ : ∀ {m n} → Ctx Tp₁ m → Ctx Tp₂ n → Sub Tm m n → Set
  Γ ⇒ Δ ⊢ σ = All₂ (λ t a → Δ ⊢ t ∈ (a / σ)) σ (toVec Γ)

-- Abstract extensions of substitutions.
record ExtensionTyped {Tp₁ Tp₂ Tm} (simple : Simple Tm)
                      (typedSub : TypedSub Tp₁ Tp₂ Tm) : Set where

  open TypedSub typedSub
  private
    module S  = SimpleExt simple
    module L₀ = Lemmas₀   (record { simple = simple })
    module C  = WeakenOps weakenOps
  open C using (_i∷_)

  field

    -- Weakens well-typed Ts.
    weaken : ∀ {n} {Δ : Ctx Tp₂ n} {t a b} → Δ ⊢ t ∈ a →
             b ∷ Δ ⊢ S.weaken t ∈ C.weaken a

    -- Weakening commutes with other substitutions.
    wk-commutes : ∀ {m n} {σ : Sub Tm m n} {t} a →
                  a / σ / S.wk ≡ a / S.wk / (t S./∷ σ)

    -- Relates weakening of types to weakening of Ts.
    /-wk : ∀ {n} {a : Tp₁ n} → a / S.wk ≡ C.weaken a

  -- A helper lemma.
  weaken-/ : ∀ {m n} {σ : Sub Tm m n} {t} a →
             C.weaken (a / σ) ≡ C.weaken a / (t S./∷ σ)
  weaken-/ {σ = σ} {t} a = begin
    C.weaken (a / σ)          ≡⟨ sym /-wk ⟩
    a / σ / S.wk              ≡⟨ wk-commutes a ⟩
    a / S.wk / (t S./∷ σ)     ≡⟨ cong₂ _/_ /-wk refl ⟩
    C.weaken a / (t S./∷ σ)   ∎

  infixr 5 _/∷_ _/i∷_

  -- Extension.
  _/∷_ : ∀ {m n} {Γ : Ctx Tp₁ m} {Δ : Ctx Tp₂ n} {t a b σ} →
         b ∷ Δ ⊢ t ∈ a / (t S./∷ σ) → Γ ⇒ Δ ⊢ σ → a ∷ Γ ⇒ b ∷ Δ ⊢ (t S./∷ σ)
  t∈a/t∷σ /∷ σ-wt =
    t∈a/t∷σ ∷ gmap₂ (subst (_⊢_∈_ _ _) (weaken-/ _) ∘ weaken) σ-wt

  -- A variant of extension tailored to _i∷_.
  _/i∷_ : ∀ {m n} {Γ : Ctx Tp₁ m} {Δ : Ctx Tp₂ n} {t a b σ} →
          b ∷ Δ ⊢ t ∈ C.weaken (a / σ) → Γ ⇒ Δ ⊢ σ → a i∷ Γ ⇒ b ∷ Δ ⊢ (t S./∷ σ)
  t∈a/σ /i∷ σ-wt =
    (subst (_⊢_∈_ _ _) (weaken-/ _) t∈a/σ) /∷ σ-wt

-- Abstract simple typed substitutions.
record SimpleTyped {Tp Tm} (simple : Simple Tm)
                   (typedSub : TypedSub Tp Tp Tm) : Set where

  field extensionTyped : ExtensionTyped simple typedSub

  open TypedSub typedSub
  open ExtensionTyped extensionTyped public
  private
    module S  = SimpleExt simple
    module L₀ = Lemmas₀ (record { simple = simple })
    module C  = WeakenOps weakenOps
  open C using (_i∷_)

  field

    -- Takes variables to well-typed Ts.
    var : ∀ {n} {Γ : Ctx Tp n} (x : Fin n) → Γ ⊢ S.var x ∈ C.lookup x Γ

    -- Types are invariant under the identity substitution.
    id-vanishes : ∀ {n} (a : Tp n) → a / S.id ≡ a

    -- Single-variable substitution is a left-inverse of weakening.
    wk-sub-vanishes : ∀ {n b} (a : Tp n) → a / S.wk / S.sub b ≡ a

  infix 10 _↑ _↑i

  -- Lifting.
  _↑ : ∀ {m n} {Γ : Ctx Tp m} {Δ : Ctx Tp n} {σ} → Γ ⇒ Δ ⊢ σ → ∀ {a} →
       a ∷ Γ ⇒ a / σ S.↑ ∷ Δ ⊢ (σ S.↑)
  σ-wt ↑ = var zero /∷ σ-wt

  -- A variant of lifting tailored to _i∷_.
  _↑i : ∀ {m n} {Γ : Ctx Tp m} {Δ : Ctx Tp n} {σ} → Γ ⇒ Δ ⊢ σ → ∀ {a} →
        a i∷ Γ ⇒ a / σ i∷ Δ ⊢ σ S.↑
  σ-wt ↑i = var zero /i∷ σ-wt

  -- The identity substitution.
  id : ∀ {n} {Γ : Ctx Tp n} → Γ ⇒ Γ ⊢ S.id
  id {zero}          = []
  id {suc n} {a ∷ Γ} =
    subst₂ (λ Δ σ → a ∷ Γ ⇒ Δ ⊢ σ)
           (cong (flip _∷_ Γ) (id-vanishes a)) (L₀.id-↑⋆ 1) (id ↑)
    where
      id-vanishes′ : ∀ {n} (a : Tp (1 + n)) → a / S.id S.↑ ≡ a
      id-vanishes′ a = begin
        a / S.id S.↑  ≡⟨ cong (_/_ a) (L₀.id-↑⋆ 1) ⟩
        a / S.id      ≡⟨ id-vanishes a ⟩
        a             ∎

  -- Weakening.
  wk : ∀ {n} {Γ : Ctx Tp n} {a} → Γ ⇒ a ∷ Γ ⊢ S.wk
  wk {n} {Γ = Γ} {a = a} =
    gmap₂₁ (weaken′ ∘ subst (_⊢_∈_ _ _) (id-vanishes _)) id
    where
      weaken′ : ∀ {n} {Γ : Ctx Tp n} {t a b} → Γ ⊢ t ∈ a →
                b ∷ Γ ⊢ S.weaken t ∈ a / S.wk
      weaken′ = subst (_⊢_∈_ _ _) (sym /-wk) ∘ weaken

  private
    wk-sub-vanishes′ : ∀ {n a} {t : Tm n} → a ≡ C.weaken a / S.sub t
    wk-sub-vanishes′ {a = a} {t} = begin
      a                      ≡⟨ sym (wk-sub-vanishes a) ⟩
      a / S.wk / S.sub t     ≡⟨ cong (flip _/_ _) /-wk ⟩
      C.weaken a / S.sub t   ∎

    id-wk-sub-vanishes : ∀ {n a} {t : Tm n} →
                         a / S.id ≡ C.weaken a / S.sub t
    id-wk-sub-vanishes {a = a} {t} = begin
      a / S.id               ≡⟨ id-vanishes a ⟩
      a                      ≡⟨ wk-sub-vanishes′ ⟩
      C.weaken a / S.sub t   ∎

  -- A substitution which only replaces the first variable.
  sub : ∀ {n} {Γ : Ctx Tp n} {t a} → Γ ⊢ t ∈ a → a i∷ Γ ⇒ Γ ⊢ S.sub t
  sub t∈a = t∈a′ ∷ gmap₂₂ (subst (_⊢_∈_ _ _) id-wk-sub-vanishes) id
    where
      t∈a′ = subst (_⊢_∈_ _ _) wk-sub-vanishes′ t∈a

  -- A variant of single-variable substitution that handles
  -- self-dependently typed variables.
  sub′ : ∀ {n} {Γ : Ctx Tp n} {t a} → Γ ⊢ t ∈ a / S.sub t →
         a ∷ Γ ⇒ Γ ⊢ S.sub t
  sub′ t∈a[/t] = t∈a[/t] ∷ gmap₂₂ (subst (_⊢_∈_ _ _) id-wk-sub-vanishes) id

  -- A substitution which only changes the type of the first variable.
  tsub : ∀ {n} {Γ : Ctx Tp n} {a b} → b ∷ Γ ⊢ S.var zero ∈ a →
         a ∷ Γ ⇒ b ∷ Γ ⊢ S.id
  tsub z∈a = z∈a′ ∷ gmap₂ (subst (_⊢_∈_ _ _) (weaken-/ _) ∘ weaken) id
    where
      z∈a′ = subst (_⊢_∈_ _ _) (sym (id-vanishes _)) z∈a

-- Abstract typed liftings from Tm₁ to Tm₂.
record LiftTyped {Tp Tm₁ Tm₂} (l : Lift Tm₁ Tm₂)
                 (typedSub : TypedSub Tp Tp Tm₁)
                 (_⊢₂_∈_   : Typing Tp Tm₂ Tp)   : Set where

  open TypedSub typedSub renaming (_⊢_∈_ to _⊢₁_∈_)
  private module L = Lift l

  -- The underlying well-typed simple Tm₁-substitutions.
  field simpleTyped : SimpleTyped L.simple typedSub

  open SimpleTyped simpleTyped public

  -- Lifts well-typed Tm₁-terms to well-typed Tm₂-terms.
  field lift : ∀ {n} {Γ : Ctx Tp n} {t a} → Γ ⊢₁ t ∈ a → Γ ⊢₂ (L.lift t) ∈ a

-- Abstract variable typings.
module VarTyping {Tp} (weakenOps : Context.WeakenOps Tp) where
  open WeakenOps weakenOps

  infix 4 _⊢Var_∈_

  -- Abstract variable typings.
  data _⊢Var_∈_ {n} (Γ : Ctx Tp n) : Fin n → Tp n → Set where
    var : ∀ x → Γ ⊢Var x ∈ lookup x Γ

-- Abstract typed variable substitutions (α-renamings).
record TypedVarSubst (Tp : ℕ → Set) : Set where
  field
    application : Application Tp Fin
    weakenOps   : WeakenOps Tp

  open VarTyping weakenOps public

  typedSub : TypedSub Tp Tp Fin
  typedSub = record
    { _⊢_∈_       = _⊢Var_∈_
    ; application = application
    ; weakenOps   = weakenOps
    }

  open TypedSub typedSub public using () renaming (_⇒_⊢_ to _⇒_⊢α_)

  open Application application       using (_/_)
  open Lemmas₄     VarLemmas.lemmas₄ using (id; wk; _⊙_)
  private module C = WeakenOps weakenOps

  field
    /-wk        : ∀ {n} {a : Tp n} → a / wk ≡ C.weaken a
    id-vanishes : ∀ {n} (a : Tp n) → a / id ≡ a
    /-⊙         : ∀ {m n k} {σ₁ : Sub Fin m n} {σ₂ : Sub Fin n k} a →
                  a / σ₁ ⊙ σ₂ ≡ a / σ₁ / σ₂

  appLemmas : AppLemmas Tp Fin
  appLemmas = record
    { application = application
    ; lemmas₄     = VarLemmas.lemmas₄
    ; id-vanishes = id-vanishes
    ; /-⊙         = /-⊙
    }

  open ExtAppLemmas appLemmas hiding (var; weaken; /-wk; id-vanishes; subst)

  -- Extensions of renamings.
  extensionTyped : ExtensionTyped VarLemmas.simple typedSub
  extensionTyped = record
    { weaken          = weaken
    ; wk-commutes     = wk-commutes
    ; /-wk            = /-wk
    }
    where
      open Applicative.Morphism using (op-<$>)

      weaken : ∀ {n} {Γ : Ctx Tp n} {x a b} → Γ ⊢Var x ∈ a →
               b ∷ Γ ⊢Var suc x ∈ C.weaken a
      weaken (var x) =
        subst (_⊢Var_∈_ _ _) (op-<$> (lookup-morphism x) _ _) (var (suc x))

  -- Simple typed renamings.
  simpleTyped : SimpleTyped VarLemmas.simple typedSub
  simpleTyped = record
    { extensionTyped  = extensionTyped
    ; var             = var
    ; id-vanishes     = id-vanishes
    ; wk-sub-vanishes = wk-sub-vanishes
    }

  open SimpleTyped simpleTyped public
    hiding (extensionTyped; var; /-wk; id-vanishes; wk-sub-vanishes)

-- Context-replacing substitutions.
record ContextSub (Tp₁ Tp₂ Tm : ℕ → Set) : Set₁ where
  infix 4 _⊢_∈_

  field
    _⊢_∈_ : Typing Tp₂ Tm Tp₁   -- the associated typing

    -- Simple Tm-substitutions (e.g. id).
    simple : Simple Tm

    -- Operations on the (source) Tp₁-context.
    weakenOps : WeakenOps Tp₁

  open Simple    simple    using (id)
  open WeakenOps weakenOps using (toVec)

  infix 4 _⇒_⊢-id

  -- Context-replacing substitutions.
  --
  -- An alternative representation for substitutions that only change
  -- the context of a well-typed Tm-term, i.e. where the underlying
  -- untyped substitution is the identity.
  _⇒_⊢-id : ∀ {n} → Ctx Tp₁ n → Ctx Tp₂ n → Set
  Γ ⇒ Δ ⊢-id = All₂ (λ t a → Δ ⊢ t ∈ a) id (toVec Γ)

-- Equivalences between (simple) typed substitutions and their
-- context-replacing counterparts.
record Equivalence {Tp₁ Tp₂ Tm} (simple : Simple Tm)
                   (typedSub : TypedSub Tp₁ Tp₂ Tm) : Set where

  open Simple     simple
  open TypedSub   typedSub

  -- The type of context substitutions participating in this
  -- equivalence.
  contextSub : ContextSub Tp₁ Tp₂ Tm
  contextSub = record
    { _⊢_∈_     = _⊢_∈_
    ; simple    = simple
    ; weakenOps = weakenOps
    }

  open ContextSub contextSub hiding (_⊢_∈_; simple)

  -- Types are invariant under the identity substitution.
  field id-vanishes : ∀ {n} (a : Tp₁ n) → a / id ≡ a

  -- There is a context substitution for every typed identity
  -- substitution.
  sound : ∀ {n} {Γ : Ctx Tp₁ n} {Δ : Ctx Tp₂ n} → Γ ⇒ Δ ⊢-id → Γ ⇒ Δ ⊢ id
  sound ρ = map₂ (subst (_⊢_∈_ _ _) (sym (id-vanishes _))) ρ

  -- There is a context substitution for every typed identity
  -- substitution.
  complete : ∀ {n} {Γ : Ctx Tp₁ n} {Δ : Ctx Tp₂ n} → Γ ⇒ Δ ⊢ id → Γ ⇒ Δ ⊢-id
  complete σ-wt = map₂ (subst (_⊢_∈_ _ _) (id-vanishes _)) σ-wt

-- Variants of some simple typed substitutions.
record ContextSimple {Tp Tm} (simple : Simple Tm)
                     (typedSub : TypedSub Tp Tp Tm) : Set where

  field simpleTyped : SimpleTyped simple typedSub

  open TypedSub typedSub hiding (_⊢_∈_)
  private
    module U = SimpleExt simple
    module C = WeakenOps weakenOps
    module S = SimpleTyped simpleTyped
  open C using (_i∷_)

  equivalence : Equivalence simple typedSub
  equivalence = record { id-vanishes = S.id-vanishes }

  open Equivalence equivalence public
  open ContextSub  contextSub  public

  infixr 5 _/∷_
  infix 10 _↑

  -- Extension.
  _/∷_ : ∀ {n} {Γ : Ctx Tp n} {Δ : Ctx Tp n} {a b} →
         b ∷ Δ ⊢ U.var zero ∈ a → Γ ⇒ Δ ⊢-id → a ∷ Γ ⇒ b ∷ Δ ⊢-id
  z∈a /∷ σ-wt = z∈a ∷ gmap₂ S.weaken σ-wt

  -- Lifting.
  _↑ : ∀ {n} {Γ : Ctx Tp n} {Δ : Ctx Tp n} → Γ ⇒ Δ ⊢-id → ∀ {a} →
       a ∷ Γ ⇒ a ∷ Δ ⊢-id
  ρ ↑ = S.var zero /∷ ρ

  -- The identity substitution.
  id : ∀ {n} {Γ : Ctx Tp n} → Γ ⇒ Γ ⊢-id
  id = complete S.id
