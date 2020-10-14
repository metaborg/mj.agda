import MJ.Classtable

import MJ.Syntax as Syntax
import MJ.Semantics.Values as Values
import MJ.Classtable.Core as Core
import MJ.Classtable.Code as Code

--
-- Substitution-free interpretation of welltyped MJ
--

module MJ.Semantics.Monadic {c} (Ct : Core.Classtable c)(ℂ : Code.Code Ct) where

open import Prelude hiding (_^_)
open import Data.Vec hiding (init; _>>=_)
open import Data.Vec.All.Properties.Extra as Vec∀++
open import Data.List hiding (null)
open import Data.List.Properties.Extra
open import Data.List.All.Properties.Extra
open import Data.List.Prefix
open import Data.List.First
open import Data.List.First.Properties
open import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Relation.Nullary.Decidable
open import Data.Star hiding (return; _>>=_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open Values Ct
open Syntax Ct
open Code Ct
open Core c
open Classtable Ct

open import MJ.Syntax.Program Ct
open import MJ.Classtable.Membership Ct
open import MJ.Types
open import MJ.LexicalScope c
open import MJ.Semantics.Environments Ct
open import MJ.Semantics.Objects Ct
open import MJ.Semantics.Objects.Flat Ct ℂ using (encoding)
open import Common.Weakening

{-
Make the object encoding API available;
-}
open ObjEncoding encoding

{-
The monad in which we define evaluation.
This encapsulates state, lexical environments, timeouts and exceptions.
-}
WSet = World c → Set

data Exception : Set where
  nullderef : Exception
  other     : Exception

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
M : Ctx → World c → WSet → Set
M Γ W A = Env Γ W → Store W → Result W A

return  : ∀ {Γ W}{A : WSet} → A W → M Γ W A
return v _ μ = returns ⊑-refl μ v

doTimeout : ∀ {Γ W}{A : WSet} → M Γ W A
doTimeout _ _ = timeout

raiseM : ∀ {Γ W}{A : WSet} → Exception → M Γ W A
raiseM exc E μ = exception ⊑-refl μ exc

sval-weaken : ∀ {W W' a} → W' ⊒ W → StoreVal W a → StoreVal W' a
sval-weaken ext (val x) = val $ weaken-val ext x
sval-weaken ext (obj cid x) = obj cid (weaken-obj cid ext x)

instance
  storeval-weakenable : ∀ {a} → Weakenable (λ W → StoreVal W a)
  storeval-weakenable = record {wk = sval-weaken }

infixl 10 _>>=_
_>>=_   : ∀ {Γ W}{A B : WSet} → M Γ W A → (∀ {W'} → A W' → M Γ W' B) →
          M Γ W B
(k >>= f) E μ with k E μ
... | exception ext μ' e = exception ext μ' e
... | timeout = timeout
... | returns ext μ' v = result-strengthen ext $ f v (All.map (wk ext) E) μ'

infixl 10 _^_
_^_  :  ∀ {Σ Γ}{A B : WSet} ⦃ w : Weakenable B ⦄ → M Γ Σ A → B Σ → M Γ Σ (A ⊗ B)
(f ^ x) E μ with (f E μ)
...  | timeout = timeout
...  | exception ext μ' e = exception ext μ' e
...  | returns ext μ' v = returns ext μ' (v , wk ext x)

_recoverWith_ : ∀ {Γ W}{A : WSet} → M Γ W A →
                (∀ {W'} → Exception → W' ⊒ W → M Γ W' A) →
                M Γ W A
(k recoverWith f) E μ with k E μ
... | timeout = timeout
... | returns ext μ' x = returns ext μ' x
... | exception ext μ' e = result-strengthen ext $ f e ext (wk ext E) μ'

store   : ∀ {Γ W a} → StoreVal W a → M Γ W (λ W' → a ∈ W')
store {Γ}{W}{a} sv E μ =
  let
    ext = ∷ʳ-⊒ a W
    μ'  = (All.map (wk ext) μ) all-∷ʳ (wk ext sv)
  in returns ext μ' (∈-∷ʳ W a)

update   : ∀ {Γ W a} → a ∈ W → StoreVal W a → M Γ W (λ W' → ⊤)
update ptr v E μ = returns ⊑-refl (μ All.[ ptr ]≔ v) tt

deref : ∀ {Γ W a} → a ∈ W → M Γ W (flip StoreVal a)
deref ptr E μ = returns ⊑-refl μ (∈-all ptr μ)

getEnv : ∀ {Γ W}{A : WSet} → (Env Γ W → M Γ W A) → M Γ W A
getEnv f E μ = f E E μ

usingEnv : ∀ {Γ Γ' W}{A : WSet} → Env Γ' W → M Γ' W A → M Γ W A
usingEnv E e = const $ e E

store*  : ∀ {Γ W as} → All (λ a → StoreVal W (vty a)) as →
          M Γ W (λ W' → All (λ a → (vty a) ∈ W') as)
store* [] = return []
store* (v ∷ vs) =
  store v ^ vs >>= λ{ (r , vs) →
  store* vs ^ r >>= λ{ (rs , r) →
  return (r ∷ rs) }}

{-
Lifting of object getter/setter into the monad
-}
read-field : ∀ {Γ : Ctx}{C W f a} → IsMember C FIELD f a → Val W (ref C) →
            M Γ W (λ W → Val W a)
read-field m null = raiseM nullderef
read-field m (ref o C<:C') E μ with ∈-all o μ
read-field m (ref o C<:C') E μ | obj cid O = returns ⊑-refl μ (getter _ O (inherit' C<:C' m))

write-field : ∀ {Γ C W f a} → IsMember C FIELD f a → Val W (ref C) → Val W a →
            M Γ W (flip Val (ref C))
write-field m null v = raiseM nullderef
write-field m (ref o s) v E μ with ∈-all o μ
write-field m (ref o s) v E μ | obj cid O =
  let
    vobj = obj cid (setter _ O (inherit' s m) v)
    μ' = μ All.[ o ]≔ vobj
  in returns ⊑-refl μ' (ref o s)

-- Get the implementation of any method definition of a class
mbody : ∀ {m ty} cid → AccMember cid METHOD m ty → InheritedMethod cid m ty
mbody cid mb with toWitness mb
... | (pid , s , d∈decls) = pid , s , ∈-all (proj₁ (first⟶∈ d∈decls)) (Implementation.mbodies (ℂ pid))

{-
Refinements of bind and return for the nested monad for command evaluation
-}
_>>=c_ : ∀ {I O O' : Ctx}{W : World c}{a} →
          M I W (λ W → Val W a ⊎ Env O W) →
          (∀ {W'} → Env O W' → M I W' (λ W → Val W a ⊎ Env O' W)) →
          M I W (λ W → Val W a ⊎ Env O' W)
m >>=c f = m >>= λ{
  (inj₁ v) → return (inj₁ v) ;
  (inj₂ E) → f E }

continue : ∀ {Γ : Ctx}{W : World c}{a} → M Γ W (λ W → Val W a ⊎ Env Γ W)
continue = getEnv λ E → return (inj₂ E)

{-
Fueled interpreter
-}
mutual

  {-
  Arguments are passed as mutable and thus have to be evaluated, after which
  we store the values in the store and we pass the references.
  -}
  eval-args : ∀ {Γ as W} → ℕ → All (Expr Γ) as → M Γ W (λ W' → All (λ a → (vty a) ∈ W') as)
  eval-args k args =
    evalₑ* k args >>= λ vs →
    store* (All.map val vs)

  {-
  Object initialization:
  Creates a default object; stores a mutable reference to it on the heap; calls the constructor
  on the resulting reference.
  -}
  constructM : ℕ → ∀ cid → ∀ {W} → M (Class.constr (Σ cid)) W (flip Val (ref cid))
  constructM k cid with ℂ cid
  constructM k cid | (implementation construct mbodies) =
    store (obj _ (defaultObject cid)) >>= λ r →
    store (val (ref r ε)) ^ r >>= λ{ (r' , r) →
    getEnv λ E →
    usingEnv (E ⊕ r') (eval-constructor k ε r construct) ^ r >>= λ{ (_ , r) →
    return $ ref r ε }}

  {-
  Constructor interpretation:
  The difficult case being the one where we have a super call.
  -}
  eval-constructor : ∀ {cid' cid W} → ℕ → Σ ⊢ cid' <: cid → (obj cid') ∈ W → Constructor cid →
                     M (constrctx cid) W (flip Val void)
  eval-constructor zero _ _ _ = doTimeout
  eval-constructor {_}{Object} (suc k) _ _ _ = return unit
  eval-constructor {_}{cls cid} (suc k) s o∈W (super args then b) =
    -- evaluate super call
    let
      s'   = s ◅◅ super ◅ ε
      super-con = Implementation.construct (ℂ (Class.parent (Σ (cls cid))))
    in
    eval-args k args ^ o∈W >>= λ{ (rvs , o∈W) → -- arguments
    getEnv λ{ (self ∷ _) →
      -- store a parent pointer for passing to super
      store (val (ref o∈W s')) ^ o∈W ^ rvs >>= λ{ ((sup , o∈W) , rvs) →
      usingEnv (sup ∷ rvs) (eval-constructor k s' o∈W super-con) >>= λ _ →

      -- evaluate own body
      eval-body k b >>= λ _ →
      return unit
    }}}
  eval-constructor {_}{cls id} (suc k) _ _ (body x) =
    eval-body k x >>= λ _ →
    return unit

  {-
  Method evaluation including super calls.
  The difficult case again being the one where we have a super call.
  -}
  eval-method : ∀ {cid m as b pid W Γ} → ℕ →
                Σ ⊢ cid <: pid → (obj cid) ∈ W →
                All (λ ty → vty ty ∈ W) as →
                InheritedMethod pid m (as , b) → M Γ W (flip Val b)
  eval-method zero _ _ _ _ = doTimeout
  eval-method (suc k) s o args (pid' , pid<:pid' , body b) =
    store (val (ref o (s ◅◅ pid<:pid'))) ^ args >>= λ{ (mutself , args) →
    usingEnv (mutself ∷ args) (eval-body k b) }
  eval-method {_}{m}{as}{b} (suc k) s o args (Object , _ , super x ⟨ _ ⟩then _) rewrite Σ-Object =
    -- calling a method on Object is improbable...
    ⊥-elim (∉Object {METHOD}{m}{(as , b)}(sound x))
  eval-method (suc k) s o args (cls pid' , pid<:pid' , super x ⟨ supargs ⟩then b) =
    let super-met = mbody (Class.parent (Σ (cls pid'))) x in
      store (val (ref o (s ◅◅ pid<:pid'))) ^ (args , o) >>= λ{ (mutself , args , o) →
      -- eval super args in method context
      usingEnv (mutself ∷ args) (eval-args k supargs) ^ (args , o) >>= λ{ (rvs , args , o) →
      -- call super
      eval-method k (s ◅◅ pid<:pid' ◅◅ super ◅ ε) o rvs super-met ^ (args , o) >>= λ{ (retv , args , o) →
      -- store the super return value to be used as a mutable local
      store (val retv) ^ (args , o) >>= λ{ (mutret , args , o) →
      -- store the mutable "this"
      store (val (ref o (s ◅◅ pid<:pid'))) ^ (mutret , args) >>= λ{ (mutself' , mutret , args) →
      -- call body
      usingEnv (mutret ∷ mutself' ∷ args) (eval-body k b) }}}}}

  {-
  evaluation of expressions
  -}
  evalₑ : ∀ {Γ : Ctx}{a} → ℕ → Expr Γ a → ∀ {W} → M Γ W (flip Val a)
  evalₑ zero _ = doTimeout

  -- primitive values
  evalₑ (suc k) unit =
    return unit

  evalₑ (suc k) (num n) =
    return (num n)

  evalₑ (suc k) null =
    return null

  -- variable lookup
  evalₑ (suc k) (var x) =
    getEnv (λ E → return $ getvar x E) >>= λ v →
    deref v >>= λ{ (val w) →
    return w }

  evalₑ (suc k) (upcast ε e) = evalₑ k e
  evalₑ (suc k) (upcast s₁@(_ ◅ _) e) = evalₑ k e >>= λ{
      (ref o s₂ ) → return $ ref o (s₂ ◅◅ s₁) ;
      null → return null
    }

  -- binary interger operations
  evalₑ (suc k) (iop f l r) =
    evalₑ k l >>= λ{ (num vₗ) →
    evalₑ k r >>= λ{ (num vᵣ) →
    return (num (f vₗ vᵣ)) }}

  -- method calls
  evalₑ (suc k) (call e _ {acc = mtd} args) =
    evalₑ k e >>= λ{
      null → raiseM nullderef ;
      r@(ref {dyn-cid} o s₁) →
        -- evaluate the arguments
        eval-args k args ^ o >>= λ{ (rvs , o) →
        -- dynamic dispatch: dynamic lookup of the method on the runtime class of the reference
        -- and execution of the call
        (eval-method k ε o rvs (mbody dyn-cid (inherit _ s₁ mtd))) }}

  -- field lookup in the heap
  evalₑ (suc k) (get e _ {_}{fld}) =
    evalₑ k e >>= λ{
      null → raiseM nullderef ;
      (ref o s) →
        deref o >>= λ{ (obj c O) →
        return (getter _ O $ inherit' s (sound fld)) }}

  -- object allocation
  evalₑ (suc k) (new C args) =
    eval-args k args >>= λ rvs →
    usingEnv rvs (constructM k C)


  {-
  Statement evaluation
  -}
  evalc : ∀ {I : Ctx}{O : Ctx}{W : World c}{a} → ℕ →
          Stmt I a O → M I W (λ W → Val W a ⊎ Env O W)

  evalc zero _ = doTimeout

  evalc (suc k) raise = raiseM other

  evalc (suc k) (block stmts) =
    eval-stmts k stmts >>=c λ _ → continue

  evalc (suc k) (try cs catch cs') =
    (evalc k cs >>=c λ _ → continue)
    recoverWith (λ e ext → evalc k cs' >>= λ _ → continue)

  -- new local variable
  evalc (suc k) (loc a) =
    store (val $ default a) >>= λ r →
    getEnv λ E → return (inj₂ (E ⊕ r))

  -- assigning to a local
  evalc (suc k) (asgn x e) =
    evalₑ k e >>= λ v →
    getEnv (λ E → return $ getvar x E) ^ v >>= λ{ (addr , v) →
    update addr (val v) >>= λ _ →
    continue }

  -- setting a field
  evalc (suc k) (set r _ {_}{fld} e) =
    evalₑ k r >>= λ{
    null → raiseM nullderef ;
    r'@(ref _ _) →
      evalₑ k e ^ r' >>= λ{ (v , r') →
      write-field (sound fld) r' v >>= λ _ →
      continue }}

  -- side-effectful expressions
  evalc (suc k) (run e) =
    evalₑ k e >>= λ _ →
    continue

  -- early returns
  evalc (suc k) (ret e) =
    evalₑ k e >>= λ v →
    return (inj₁ v)

  -- if-then-else blocks
  evalc (suc k) (if e then cs else ds) =
    evalₑ k e >>= λ{
      (num zero) → evalc k cs ;
      (num (suc _)) → evalc k ds
    }

  -- while loops
  evalc (suc k) (while e run b) =
    evalₑ (suc k) e >>= λ{
      (num zero)    → evalc k b >>= λ _ → evalc k (while e run b) ;
      (num (suc _)) → continue
    }

  {-
  An helper for interpreting a sequence of statements
  -}
  eval-stmts : ∀ {Γ Γ' W a} → ℕ → Stmts Γ a Γ' → M Γ W (λ W → Val W a ⊎ Env Γ' W)
  eval-stmts k ε = continue
  eval-stmts k (x ◅ st) =
    evalc k x >>=c λ E' →
    usingEnv E' (eval-stmts k st)

  {-
  An helper for interpreting method bodies (i.e. sequence of Stmts optionally followed by a return).
  -}
  eval-body : ∀ {I : Ctx}{W : World c}{a} → ℕ → Body I a → M I W (λ W → Val W a)
  eval-body k (body ε re) = evalₑ k re
  eval-body k (body stmts@(_ ◅ _) e) =
    (eval-stmts k stmts) >>= λ{
      (inj₁ v) → return v ;
      (inj₂ E) → usingEnv E (evalₑ k e) }

  {-
  An helper for interpreting a list of expressions in the same context.
  -}
  evalₑ* : ∀ {Γ W as} → ℕ → All (Expr Γ) as → M Γ W (λ W → All (Val W) as)
  evalₑ* k [] = return []
  evalₑ* k (e ∷ es) =
    evalₑ k e >>= λ v →
    evalₑ* k es ^ v >>= λ{ (vs , v) →
    return (v ∷ vs) }

eval : ∀ {a} → ℕ → Prog a → Result [] (flip Val a)
eval k (lib , main) = eval-body k main [] []

{-
a few predicates on program interpretation:
... saying it will terminate succesfully in a state where P holds
-}
_⇓⟨_⟩_ : ∀ {a} → Prog a → ℕ → (P : ∀ {W} → Val W a → Set) → Set
p ⇓⟨ k ⟩ P with eval k p
p ⇓⟨ k ⟩ P | exception _ _ _ = ⊥
p ⇓⟨ k ⟩ P | timeout = ⊥
p ⇓⟨ k ⟩ P | returns ext μ v = P v

{-
...saying it will raise an exception in a state where P holds
-}
_⇓⟨_⟩!_ : ∀ {a} → Prog a → ℕ → (P : ∀ {W} → Store W → Exception → Set) → Set
p ⇓⟨ k ⟩! P with eval k p
p ⇓⟨ k ⟩! P | exception _ μ e = P μ e
p ⇓⟨ k ⟩! P | timeout = ⊥
p ⇓⟨ k ⟩! P | returns ext μ v = ⊥
