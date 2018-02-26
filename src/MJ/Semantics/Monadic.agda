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
open import Data.Vec hiding (init; _>>=_; _∈_)
open import Data.Vec.All.Properties.Extra as Vec∀++
open import Data.List.Most
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

open import Data.Maybe using (Maybe; just; nothing)
returns-val : ∀ {W A} → Result W A → Maybe (∃ λ W' → A W')
returns-val (exception x x₁ x₂) = nothing
returns-val timeout = nothing
returns-val (returns _ _ v) = just (_ , v)

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
... | returns ext μ' v = result-strengthen ext $ f v (map-all (wk ext) E) μ'

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
    μ'  = (map-all (wk ext) μ) all-∷ʳ (wk ext sv)
  in returns ext μ' (∈-∷ʳ W a)

update   : ∀ {Γ W a} → a ∈ W → StoreVal W a → M Γ W (λ W' → ⊤)
update ptr v E μ = returns ⊑-refl (μ All[ ptr ]≔' v) tt

deref : ∀ {Γ W a} → a ∈ W → M Γ W (flip StoreVal a)
deref ptr E μ = returns ⊑-refl μ (∈-all ptr μ)

getEnv : ∀ {Γ W}{A : WSet} → (Env Γ W → M Γ W A) → M Γ W A
getEnv f E μ = f E E μ

usingEnv : ∀ {Γ Γ' W}{A : WSet} → Env Γ' W → M Γ' W A → M Γ W A
usingEnv E e = const $ e E

store*  : ∀ {Γ W as} → All (λ a → StoreVal W (vty a)) as →
          M Γ W (λ W' → All (λ a → (vty a) ∈ W') as)
store* [] = return []
store* (v ∷ vs) = do
  (r , vs) ← store v ^ vs
  (rs , r) ← store* vs ^ r
  return (r ∷ rs)

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
    μ' = μ All[ o ]≔' vobj
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
m >>=c f = m >>= λ where
  (inj₁ v) → return (inj₁ v)
  (inj₂ E) → f E

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
  eval-args k args = do
    vs ← evalₑ* k args
    store* (map-all val vs)

  {-
  Object initialization:
  Creates a default object; stores a mutable reference to it on the heap; calls the constructor
  on the resulting reference.
  -}
  constructM : ℕ → ∀ cid → ∀ {W} → M (Class.constr (Σ cid)) W (flip Val (ref cid))
  constructM k cid with ℂ cid
  constructM k cid | (implementation construct mbodies) = do
    r      ← store (obj _ (defaultObject cid))
    r' , r ← store (val (ref r ε)) ^ r
    _  , r ← getEnv λ E → usingEnv (r' ∷ E) (eval-constructor k ε r construct) ^ r
    return (ref r ε)

  {-
  Constructor interpretation:
  The difficult case being the one where we have a super call.
  -}
  eval-constructor : ∀ {cid' cid W} → ℕ → Σ ⊢ cid' <: cid → (obj cid') ∈ W → Constructor cid →
                     M (constrctx cid) W (flip Val void)
  eval-constructor zero _ _ _ = doTimeout
  eval-constructor {_}{Object} (suc k) _ _ _ = return unit
  eval-constructor {_}{cls cid} (suc k) s o∈W (super args then b) = do
    let s' = s ◅◅ super ◅ ε
    let super-con = Implementation.construct (ℂ (Class.parent (Σ (cls cid))))
    -- eval the super arguments
    rvs , o∈W ← eval-args k args ^ o∈W
    -- store a parent pointer for passing to super
    getEnv λ where
      (self ∷ _) → do
        sup , o∈W , rvs ← store (val (ref o∈W s')) ^ (o∈W , rvs)
        _ ← usingEnv (sup ∷ rvs) (eval-constructor k s' o∈W super-con)
        -- evaluate own body
        _ ← eval-body k b
        return unit

  eval-constructor {_}{cls id} (suc k) _ _ (body x) = do
    _ ← eval-body k x
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

  eval-method (suc k) s o args (pid' , pid<:pid' , body b) = do
    mutself , args ← store (val (ref o (s ◅◅ pid<:pid'))) ^ args
    usingEnv (mutself ∷ args) (eval-body k b)

  -- calling a method on Object is improbable...
  eval-method {_}{m}{as}{b} (suc k) s o args (Object , _ , super x ⟨ _ ⟩then _) rewrite Σ-Object =
    ⊥-elim (∉Object {METHOD}{m}{(as , b)}(sound x))

  eval-method (suc k) s o args (cls pid' , pid<:pid' , super x ⟨ supargs ⟩then b) = do
      let super-met = mbody (Class.parent (Σ (cls pid'))) x
      -- store a cast this-reference
      mutself , args , o       ← store (val (ref o (s ◅◅ pid<:pid'))) ^ (args , o)
      -- eval super args in method context
      rvs , args , o           ← usingEnv (mutself ∷ args) (eval-args k supargs) ^ (args , o)
      -- call super
      retv , args , o          ← eval-method k (s ◅◅ pid<:pid' ◅◅ super ◅ ε) o rvs super-met ^ (args , o)
      -- store the super return value to be used as a mutable local
      mutret , args , o        ← store (val retv) ^ (args , o)
      -- store the cast this-reference
      mutself' , mutret , args ← store (val (ref o (s ◅◅ pid<:pid'))) ^ (mutret , args)
      -- call body
      usingEnv (mutret ∷ mutself' ∷ args) (eval-body k b)

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
  evalₑ (suc k) (var x) = do
    v     ← getEnv (λ E → return $ ∈-all x E)
    val w ← deref v
    return w

  evalₑ (suc k) (upcast ε e) = evalₑ k e
  evalₑ (suc k) (upcast s₁@(_ ◅ _) e) = do
    (ref o s₂ ) ← evalₑ k e where null → return null
    return $ ref o (s₂ ◅◅ s₁)

  -- binary interger operations
  evalₑ (suc k) (iop f l r) = do
    num vₗ ← evalₑ k l
    num vᵣ ← evalₑ k r
    return (num (f vₗ vᵣ))

  -- method calls
  evalₑ (suc k) (call e _ {acc = mtd} args) = do
    ref {dyn-cid} o s₁ ← evalₑ k e where null → raiseM nullderef
    -- evaluate the arguments
    rvs , o            ← eval-args k args ^ o
    -- dynamic dispatch: dynamic lookup of the method on the runtime class of the reference
    -- and execution of the call
    (eval-method k ε o rvs (mbody dyn-cid (inherit _ s₁ mtd)))

  -- field lookup in the heap
  evalₑ (suc k) (get e _ {_}{fld}) = do
    ref o s ← evalₑ k e where null → raiseM nullderef
    obj c O ← deref o
    return (getter _ O $ inherit' s (sound fld))

  -- object allocation
  evalₑ (suc k) (new C args) = do
    rvs ← eval-args k args
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
    recoverWith λ e ext → do
      _ ← evalc k cs'
      continue

  -- new local variable
  evalc (suc k) (loc a) = do
    r ← store (val $ default a)
    getEnv λ E → return (inj₂ (r ∷ E))

  -- assigning to a local
  evalc (suc k) (asgn x e) = do
    v        ← evalₑ k e
    addr , v ← getEnv (λ E → return $ ∈-all x E) ^ v
    _        ← update addr (val v)
    continue

  -- setting a field
  evalc (suc k) (set r _ {_}{fld} e) = do
    r'@(ref _ _) ← evalₑ k r where null → raiseM nullderef
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
  evalc (suc k) (if e then cs else ds) =
    evalₑ k e >>= λ where
      (num zero) → evalc k cs
      (num (suc _)) → evalc k ds

  -- while loops
  evalc (suc k) (while e run b) =
    evalₑ (suc k) e >>= λ where
      (num (suc _)) → continue
      (num zero)    → do
        _ ← evalc k b
        evalc k (while e run b)

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
    eval-stmts k stmts >>= λ where
      (inj₁ v) → return v
      (inj₂ E) → usingEnv E (evalₑ k e)

  {-
  An helper for interpreting a list of expressions in the same context.
  -}
  evalₑ* : ∀ {Γ W as} → ℕ → All (Expr Γ) as → M Γ W (λ W → All (Val W) as)
  evalₑ* k [] = return []
  evalₑ* k (e ∷ es) = do
    v      ← evalₑ k e
    vs , v ← evalₑ* k es ^ v
    return (v ∷ vs)

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
