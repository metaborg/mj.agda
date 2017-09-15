import MJ.Classtable

import MJ.Syntax as Syntax
import MJ.Semantics.Values as Values
import MJ.Classtable.Core as Core

--
-- Substitution-free interpretation of welltyped MJ
--

module MJ.Semantics.Monadic {c} (Ct : Core.Classtable c)(ℂ : Syntax.Classes Ct) where

open import Prelude
open import Data.Vec hiding (init; _>>=_; _∈_)
open import Data.Vec.All.Properties.Extra as Vec∀++
open import Data.List.Most
open import Relation.Nullary.Decidable
open import Data.Star hiding (return; _>>=_)

import Data.Vec.All as Vec∀

open Values Ct
open Syntax Ct
open Core c
open Classtable Ct

open import MJ.Classtable.Membership Ct
open import MJ.Types
open import MJ.LexicalScope Ct
open import MJ.Semantics.Objects.Flat Ct ℂ using (encoding)
open import MJ.Semantics.Weakenable
open Weakenable ⦃...⦄

open ObjEncoding encoding

WSet = World c → Set

data Exception : Set where
  earlyRet : Exception
  other    : Exception

data Result (W : World c)(A : WSet) : Set where
  exception : ∀ {W'} → W' ⊒ W → Store W' → Exception → Result W A
  timeout   : Result W A
  returns   : ∀ {W'} → W' ⊒ W → Store W' → A W' → Result W A

result-strengthen : ∀ {W W'}{A : WSet} → W ⊒ W' → Result W A → Result W' A
result-strengthen ext (exception ext' μ e) = exception (ext ⊚ ext') μ e
result-strengthen ext timeout = timeout
result-strengthen ext (returns ext' μ v) = returns (ext ⊚ ext') μ v

-- monad that threads a readonly environment, store and propagates
-- semantic errors
EvalM : Ctx → World c → WSet → Set
EvalM Γ W A = Env Γ W → Store W → Result W A

return  : ∀ {Γ W}{A : WSet} → A W → EvalM Γ W A
return v _ μ = returns ⊑-refl μ v

doTimeout : ∀ {Γ W}{A : WSet} → EvalM Γ W A
doTimeout _ _ = timeout

raiseM : ∀ {Γ W}{A : WSet} → Exception → EvalM Γ W A
raiseM exc E μ = exception ⊑-refl μ exc

sval-weaken : ∀ {W W' a} → W' ⊒ W → StoreVal W a → StoreVal W' a
sval-weaken ext (val x) = val $ weaken-val ext x
sval-weaken ext (obj cid x) = obj cid (weaken-obj cid ext x)

instance
  storeval-weakenable : ∀ {a} → Weakenable (λ W → StoreVal W a)
  storeval-weakenable = record {
    weaken = sval-weaken }

infixl 10 _>>=_
_>>=_   : ∀ {Γ W}{A B : WSet} → EvalM Γ W A → (∀ {W'} ⦃ p : IsIncludedOnce W W' ⦄ → A W' → W' ⊒ W → EvalM Γ W' B) →
          EvalM Γ W B
(k >>= f) E μ with k E μ
... | exception ext μ' e = exception ext μ' e
... | timeout = timeout
... | returns ext μ' v = result-strengthen ext $ f ⦃ record { is-included-once = ext } ⦄ v ext (map-all (weaken ext) E) μ'

_recoverWith_ : ∀ {Γ W}{A : WSet} → EvalM Γ W A →
                (∀ {W'} → Exception → W' ⊒ W → EvalM Γ W' A) →
                EvalM Γ W A
(k recoverWith f) E μ with k E μ
... | timeout = timeout
... | returns ext μ' x = returns ext μ' x
... | exception ext μ' e = result-strengthen ext $ f e ext (weaken ext E) μ'

store   : ∀ {Γ W a} → StoreVal W a → EvalM Γ W (λ W' → a ∈ W')
store {Γ}{W}{a} sv E μ =
  let
    ext = ∷ʳ-⊒ a W
    μ'  = (map-all (weaken ext) μ) all-∷ʳ (weaken ext sv)
  in returns ext μ' (∈-∷ʳ W a)

update   : ∀ {Γ W a} → a ∈ W → StoreVal W a → EvalM Γ W (λ W' → ⊤)
update ptr v E μ = returns ⊑-refl (μ All[ ptr ]≔' v) tt

deref : ∀ {Γ W a} → a ∈ W → EvalM Γ W (flip StoreVal a)
deref ptr E μ = returns ⊑-refl μ (∈-all ptr μ)

getEnv : ∀ {Γ W}{A : WSet} → (Env Γ W → EvalM Γ W A) → EvalM Γ W A
getEnv f E μ = f E E μ

usingEnv : ∀ {Γ Γ' W}{A : WSet} → Env Γ' W → EvalM Γ' W A → EvalM Γ W A
usingEnv E e = const $ e E

store*  : ∀ {Γ W as} → All (λ a → StoreVal W (vty a)) as →
          EvalM Γ W (λ W' → All (λ a → (vty a) ∈ W') as)
store* [] = return []
store* (v ∷ vs) =
  store v >>= λ {W'} r w₀ →
  store* (weaken w₀ vs) >>= λ rs w₁ →
  return (weaken w₁ r ∷ rs)

read-field : ∀ {Γ : Ctx}{C W f a} → IsMember C FIELD f a → Val W (ref C) →
            EvalM Γ W (λ W → Val W a)
read-field m null = raiseM other
read-field m (ref o C<:C') E μ with ∈-all o μ
read-field m (ref o C<:C') E μ | obj cid O = returns ⊑-refl μ (getter _ O (inherit' C<:C' m))

write-field : ∀ {Γ C W f a} → IsMember C FIELD f a → Val W (ref C) → Val W a →
            EvalM Γ W (flip Val (ref C))
write-field m null v = raiseM other
write-field m (ref o s) v E μ with ∈-all o μ
write-field m (ref o s) v E μ | obj cid O =
  let
    vobj = obj cid (setter _ O (inherit' s m) v)
    μ' = μ All[ o ]≔' vobj
  in returns ⊑-refl μ' (ref o s)

-- Get the implementation of any method definition of a class
mbody : ∀ {m ty} cid → AccMember cid METHOD m ty → InheritedMethod cid m ty
mbody cid mb with toWitness mb
... | (pid , s , d∈decls) = pid , s , ∈-all (proj₁ (first⟶∈ d∈decls)) (Implementation.mbodies (ℂ pid))

mutual

  --
  -- object initialization
  --

  eval-args : ∀ {Γ as W} → All (Expr Γ) as → EvalM Γ W (λ W' → All (λ a → (vty a) ∈ W') as)
  eval-args args = evalₑ* args >>= λ vs w₁ → store* (map-all val vs)

  constructM : ∀ cid → ∀ {W} → EvalM (Class.constr (Σ cid)) W (flip Val (ref cid))
  constructM cid with ℂ cid
  constructM cid | (implementation construct mbodies) =
    store (obj _ (defaultObject cid)) >>= λ r _ →
    store (val (ref r ε)) >>= λ r' w₁ →
    getEnv λ E →
    usingEnv (E ⊕ r') (eval-constructor ε (weaken w₁ r) construct) >>= λ _ w₂ →
    return $ ref (weaken (w₁ ⊚ w₂) r) ε

  eval-constructor : ∀ {cid' cid W} → Σ ⊢ cid' <: cid → (obj cid') ∈ W → Constructor cid → EvalM (constrctx cid) W (flip Val void)
  eval-constructor {_}{Object} _ _ _ = return unit
  eval-constructor {_}{cls cid} s o∈W (super args then b) =
    -- evaluate super call
    let super-con = Implementation.construct (ℂ (Class.parent (Σ (cls cid)))) in
    eval-args args >>= λ rvs w₀ → -- arguments
    getEnv λ{ (self ∷ _) →
      let
        o∈W' = weaken w₀ o∈W
        s'   = s ◅◅ super ◅ ε
      in
      store (val (ref o∈W' s')) >>= λ sup w₁ → -- store a parent pointer for passing to super
      usingEnv (sup ∷ weaken w₁ rvs) (eval-constructor s' (weaken w₁ o∈W') super-con) >>= λ _ _ →

      -- evaluate own body
      eval-body b >>= λ _ _ →
      return unit
    }
  eval-constructor {_}{cls id} _ _ (body x) = eval-body x >>= λ _ _ → return unit

  eval-method : ∀ {cid m as b pid W Γ} →
                Σ ⊢ cid <: pid → (obj cid) ∈ W →
                All (λ ty → vty ty ∈ W) as →
                InheritedMethod pid m (as , b) → EvalM Γ W (flip Val b)
  eval-method {_}{m}{as}{b} s o args (Object , _ , super x ⟨ _ ⟩then _) rewrite Σ-Object =
    -- calling a method on Object is improbable...
    ⊥-elim (∉Object {METHOD}{m}{(as , b)}(sound x))
  eval-method s o args (cls pid' , pid<:pid' , super x ⟨ supargs ⟩then b) =
    let super-met = mbody (Class.parent (Σ (cls pid'))) x in
      store (val (ref o (s ◅◅ pid<:pid'))) >>= λ mutself w₀ →
      -- eval super args in method context
      usingEnv (mutself ∷ weaken w₀ args) (eval-args supargs) >>= λ rvs w₁ →
      -- call super
      eval-method (s ◅◅ pid<:pid' ◅◅ super ◅ ε) (weaken (w₀ ⊚ w₁) o) rvs super-met >>= λ ret w₂ →
      -- store the super return value to be used as a mutable local
      store (val ret) >>= λ mutret w₃ →
      -- store the mutable "this"
      store (val (ref (weaken (w₀ ⊚ w₁ ⊚ w₂ ⊚ w₃) o) (s ◅◅ pid<:pid'))) >>= λ mutself' w₄ →
      -- call body
      usingEnv ((weaken w₄ mutret ∷ mutself' ∷ weaken (w₀ ⊚ w₁ ⊚ w₂ ⊚ w₃ ⊚ w₄) args)) (eval-body b)
  eval-method s o args (pid' , pid<:pid' , body b) =
    store (val (ref o (s ◅◅ pid<:pid'))) >>= λ mutself w →
    usingEnv (mutself ∷ weaken w args) (eval-body b)

  --
  -- evaluation of expressions
  --

  {-# TERMINATING #-}
  evalₑ : ∀ {Γ : Ctx}{a} → Expr Γ a → ∀ {W} → EvalM Γ W (flip Val a)

  -- primitive values
  evalₑ unit =
    return unit

  evalₑ (num n) =
    return (num n)

  evalₑ null =
    return null

  -- variable lookup
  evalₑ (var x) =
    getEnv (λ E → return $ getvar x E) >>= λ v _ →
    deref v >>= λ{ (val w) _ →
    return w }

  evalₑ (upcast ε e) = evalₑ e
  evalₑ (upcast s₁@(_ ◅ _) e) = evalₑ e >>= λ{
      (ref o s₂ ) w → return $ ref o (s₂ ◅◅ s₁) ;
      null w → return null
    }

  -- binary interger operations
  evalₑ (iop f l r) =
    evalₑ l >>= λ{ (num vₗ) _ →
    evalₑ r >>= λ{ (num vᵣ) _ →
    return (num (f vₗ vᵣ)) }}

  -- method calls
  evalₑ (call e _ {acc = mtd} args) =
    evalₑ e >>= λ{
      null _ → raiseM other ;
      r@(ref {dyn-cid} o s₁) w₁ →
        -- evaluate the arguments
        eval-args args >>= λ rvs w₂ →
        store (val (ref (weaken w₂ o) ε)) >>= λ mutself w₃ →
        -- dynamic lookup of the method on the runtime class of the reference
        -- and execution of the call
        eval-method ε (weaken (w₂ ⊚ w₃) o) (weaken w₃ rvs) (mbody dyn-cid (inherit _ s₁ mtd))
    }

  -- field lookup in the heap
  evalₑ (get e _ {_}{fld}) =
    evalₑ e >>= λ{
      null _ → raiseM other ;
      (ref o s) w₁ →
      deref o >>= λ{ (obj c O) _ →
      return (getter _ O $ inherit' s (sound fld)) }}

  -- object allocation
  evalₑ (new C args) =
    eval-args args >>= λ rvs _ →
    usingEnv rvs (constructM C)

  --
  -- command evaluation
  --

  evalc : ∀ {I : Ctx}{O : Ctx}{W : World c}{a} →
          Stmt I a O → EvalM I W (λ W → Env O W)

  evalc raise = raiseM other

  evalc (block stmts) =
    eval-stmts stmts >>= λ _ _ → getEnv return

  evalc (try cs catch cs') =
    (evalc cs >>= λ _ _ → getEnv return)
    recoverWith (λ e ext → evalc cs' >>= λ _ _ → getEnv return)

  -- new local variable
  evalc (loc a) =
    store (val $ default a) >>= λ r w →
    getEnv λ E → return (E ⊕ r)

  -- assigning to a local
  evalc (asgn x e) =
    evalₑ e >>= λ v w₁ →
    getEnv (λ E → return $ getvar x E) >>= λ addr w₂ →
    update addr (val (weaken w₂ v )) >>= λ _ _ →
    getEnv return

  -- setting a field
  evalc (set r _ {_}{fld} e) =
    evalₑ r >>= λ{ null _ → raiseM other ; r@(ref _ _) w₁ →
    evalₑ e >>= λ v w₂ →
    write-field (sound fld) (weaken w₂ r) v >>= λ _ _ →
    getEnv return }

  -- side-effectful expressions
  evalc (do e) =
    evalₑ e >>= λ _ _ →
    getEnv return

  -- early returns
  evalc (ret x) = raiseM earlyRet

  -- while loops
  evalc (while e do b) =
    evalₑ e >>= λ{
      (num zero)    w → evalc b >>= λ _ _ → evalc (while e do b) ;
      (num (suc _)) w → getEnv return
    }

  -- evaluating a method body
  eval-body : ∀ {I : Ctx}{W : World c}{a} → Body I a → EvalM I W (λ W → Val W a)
  eval-body (body ε re) = evalₑ re
  eval-body (body stmts@(_ ◅ _) e) =
    eval-stmts stmts >>= λ E' _ →
    usingEnv E' (evalₑ e)

  evalₑ* : ∀ {Γ W as} → All (Expr Γ) as → EvalM Γ W (λ W → All (Val W) as)
  evalₑ* [] = return []
  evalₑ* (e ∷ es) =
    evalₑ e >>= λ v _ →
    evalₑ* es >>= λ vs w →
    return (weaken w v ∷ vs)

  eval-stmts : ∀ {Γ Γ' W a} → Stmts Γ a Γ' → EvalM Γ W (λ W → Env Γ' W)
  eval-stmts ε = getEnv return
  eval-stmts (x ◅ st) =
    evalc x >>= λ E' _ →
    usingEnv E' (eval-stmts st)

  -- evaluating a program
  eval : ∀ {a} → Prog a → Result [] (flip Val a)
  eval (lib , main) = eval-body main [] []

-- a few predicates on programs:
-- ... saying it will terminate succesfully in a state where P holds
_⇓_ : ∀ {a} → Prog a → (P : ∀ {W} → Val W a → Set) → Set
p ⇓ P with eval p
p ⇓ P | exception _ _ _ = ⊥
p ⇓ P | timeout = ⊥
p ⇓ P | returns ext μ v = P v

-- ...saying it will raise an exception in a state where P holds
_⇓!_ : ∀ {a} → Prog a → (P : ∀ {W} → Store W → Exception → Set) → Set
p ⇓! P with eval p
p ⇓! P | exception _ μ e = P μ e
p ⇓! P | timeout = ⊥
p ⇓! P | returns ext μ v = ⊥
