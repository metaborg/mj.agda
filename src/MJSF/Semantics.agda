open import Data.Nat hiding (_+_ ; _^_)
open import Data.Integer
open import Data.Fin using (Fin; #_; suc; zero)
open import Data.List.Most
open import Data.Product hiding (map)
open import Data.List.All as List∀ hiding (lookup ; map)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Data.List.Any hiding (map)
open import Data.Unit
open import Data.Empty
open import Common.Weakening
open import Common.Strength
open import Data.List.Prefix
open import Data.List.Properties.Extra
open import Data.List.All.Properties.Extra
open import Data.Maybe hiding (All ; map)
open import Data.Star hiding (return ; _>>=_ ; map)


module MJSF.Semantics (k : ℕ) where

Scope : Set
Scope = Fin k


-----------
-- TYPES --
-----------

data VTy : Set where
  void : VTy;  int : VTy;  ref : Scope → VTy

data Ty : Set where
  vᵗ : VTy → Ty;  mᵗ : List VTy → VTy → Ty;  cᵗ : Scope → Scope → Ty 


-------------
-- HAS TAG --
-------------

-- predicates for distinguishing tags (used for saying that a
-- particular list of declarations contain *only* declarations of a
-- particular tag).

data #v : (VTy → Set) → Ty → Set where
  #v' : ∀ {t p} → p t → #v p (vᵗ t)

data #m : (List VTy → VTy → Set) → Ty → Set where
  #m' : ∀ {ts rt p} → p ts rt → #m p (mᵗ ts rt)

open import ScopeGraph.ScopesFrames k Ty hiding (Scope)

module Syntax (g : Graph) where

  open UsesGraph g


  -------------------------------
  -- SUBTYPING AND INHERITANCE --
  -------------------------------

  data _<:_ : VTy → VTy → Set where
    refl   :  ∀ {t} → t <: t
    super  :  ∀ {s1 s2 t} →
              s2 ∈ edgesOf s1 → (ref s2) <: t → (ref s1) <: t

  <:-trans : ∀{t1 t2 t3} → t1 <: t2 → t2 <: t3 → t1 <: t3
  <:-trans refl           p = p
  <:-trans (super edge p) q = super edge (<:-trans p q)


  ------------
  -- SYNTAX --
  ------------

  mutual
    data Expr (s : Scope) : VTy → Set where
      call     :  ∀ {s' ts t} → Expr<: s (ref s') →
                  (s' ↦ (mᵗ (ref s' ∷ ts) t)) →
                  All (Expr<: s) ts → Expr s t
      get      :  ∀ {s' t} → Expr<: s (ref s') → (s' ↦ vᵗ t) → Expr s t
      var      :  ∀ {t} → (s ↦ vᵗ t) → Expr s t
      new      :  ∀ {sʳ s'} → s ↦ cᵗ sʳ s' → Expr s (ref s')
      null     :  ∀ {s'} → Expr s (ref s')
      num      :  ℤ → Expr s int
      iop      :  (ℤ → ℤ → ℤ) → (l r : Expr<: s int) → Expr s int

    data Expr<: (s : Scope) (t : VTy) : Set where
      upcast  : ∀ {t'} →
                t' <: t → Expr s t' → Expr<: s t

  data Stmt (s : Scope) : Scope → Set where
    loc  : ∀ (s' : Scope)(t' : VTy)⦃ shape : g s' ≡ ([ vᵗ t' ] , [ s ]) ⦄ → Stmt s s'
    asgn : ∀ {t'} → (s ↦ vᵗ t') → Expr<: s t' → Stmt s s
    set  : ∀ {s' t'} → Expr<: s (ref s') → (s' ↦ vᵗ t') → Expr<: s t' → Stmt s s
    do   : ∀ {t'} → Expr<: s t' → Stmt s s

  Stmts : Scope → Scope → Set
  Stmts = Star Stmt

  data Body (s : Scope) : VTy → Set where
    body      : ∀ {s' t} → Stmts s s' → Expr<: s' t → Body s t
    body-void : ∀ {s'} → Stmts s s' → Body s void

  data Meth (s : Scope) : List VTy →  VTy → Set where
    meth  :  ∀ {ts rt}(s' : Scope)
             ⦃ shape : g s' ≡ (vᵗ (ref s) ∷ (map vᵗ ts) , [ s ]) ⦄ →
             Body s' rt →
             Meth s (ref s ∷ ts) rt

  data Class (sʳ s : Scope) : Set where
    class1  :  ∀ {ms fs sᵖ}{oms : List (List VTy × VTy)} →
               sʳ ↦ (cᵗ sʳ sᵖ) →
               ⦃ shape  :  g s  ≡  (ms ++ fs ,  sʳ ∷ sᵖ ∷ []) ⦄ →
               All (#m (Meth s)) ms →
               All (#v (λ _ → ⊤)) fs →
               All (λ{ (ts , rt) → (s ↦ (mᵗ ts rt)) × Meth s ts rt }) oms →
               Class sʳ s
    class0 : ∀ {ms fs}{oms : List (List VTy × VTy)} →
             ⦃ shape : g s ≡ (ms ++ fs , [ sʳ ]) ⦄ →
             All (#m (Meth s)) ms →   -- only methods
             All (#v (λ _ → ⊤)) fs →  -- only values
             All (λ{ (ts , rt) → (s ↦ (mᵗ ts rt)) × Meth s ts rt }) oms → -- overrides
             Class sʳ s

  data Program : Set where
    program :
      ∀ {sʳ cs}⦃ shape : g sʳ ≡ (cs , []) ⦄ → All (λ{ (cᵗ sʳ s) → Class sʳ s ; _ → ⊥ }) cs → Program


  ------------
  -- VALUES --
  ------------

  data Val : VTy → List Scope → Set where
    ref    :  ∀ {s Σ} → Frame s Σ → Val (ref s) Σ
    null   :  ∀ {s Σ} → Val (ref s) Σ
    num    :  ∀ {Σ} → ℤ → Val int Σ
    void   :  ∀ {Σ} → Val void Σ

  data Val<: (t : VTy) (Σ : List Scope) : Set where
    upcast  :  ∀ {t'} → (t' <: t) → Val t' Σ → Val<: t Σ

  reflv : ∀ {t Σ} → Val t Σ → Val<: t Σ
  reflv v = upcast refl v

  data Valᵗ : Ty → List Scope → Set where
    cᵗ : ∀ {sʳ s Σ} → Class sʳ s → Frame sʳ Σ → Valᵗ (cᵗ sʳ s) Σ
    mᵗ : ∀ {s ts rt Σ} → Meth s ts rt → Valᵗ (mᵗ ts rt) Σ
    vᵗ : ∀ {t Σ} → Val<: t Σ → Valᵗ (vᵗ t) Σ


  ---------------
  -- WEAKENING --
  ---------------

  open Weakenable ⦃...⦄

  val-weaken    :  ∀ {t Σ Σ'} → Σ ⊑ Σ' → Val t Σ → Val t Σ'
  val-weaken ext (num i)  =  num i
  val-weaken ext (ref f)  =  ref (wk ext f)
  val-weaken ext null     =  null
  val-weaken ext void     =  void

  val<:-weaken  :  ∀ {t Σ Σ'} → Σ ⊑ Σ' → Val<: t Σ → Val<: t Σ'
  val<:-weaken ext (upcast σ v)  =  upcast σ (val-weaken ext v)

  instance
    val<:-weakenable : ∀ {t} → Weakenable (Val<: t)
    val<:-weakenable = record { wk = val<:-weaken }

  valᵗ-weaken : ∀ {t Σ Σ'} → Σ ⊑ Σ' → Valᵗ t Σ → Valᵗ t Σ'
  valᵗ-weaken ext (vᵗ v)    =  vᵗ (val<:-weaken ext v)
  valᵗ-weaken ext (mᵗ m)    =  mᵗ m
  valᵗ-weaken ext (cᵗ c f)  =  cᵗ c (wk ext f)


  open UsesVal Valᵗ valᵗ-weaken renaming (getFrame to getFrame')


  ----------------------------
  -- UPCASTING AND COERCION --
  ----------------------------

  up<: : ∀ {t t' Σ} → t <: t' → Val<: t Σ → Val<: t' Σ
  up<: σ (upcast σ' v) = upcast (<:-trans σ' σ) v

  coerce<: : ∀ {t t' Σ} → t <: t' → Val t Σ → Heap Σ → Val t' Σ
  coerce<: refl v h = v
  coerce<: (super edge σ) null h = coerce<: σ null h
  coerce<: (super edge σ) (ref f) h
    with (List∀.lookup h f)
  ...  | (_ , links)  =  coerce<: σ (ref (List∀.lookup links edge)) h

  coerce : ∀ {t Σ} → Val<: t Σ → Heap Σ → Val t Σ
  coerce (upcast σ v) h  =  coerce<: σ v h


  -----------
  -- MONAD --
  -----------

  data Res (a : Set) : Set where timeout : Res a  ;  nullpointer : Res a  ;  ok : (x : a) → Res a

  M : (s : Scope) → (List Scope → Set) → List Scope → Set
  M s p Σ = Frame s Σ → Heap Σ → Res (∃ λ Σ' → (Heap Σ' × p Σ' × Σ ⊑ Σ'))

  _>>=_     :  ∀ {s Σ}{p q : List Scope → Set} →
               M s p Σ → (∀ {Σ'} → p Σ' → M s q Σ') → M s q Σ
  (a >>= b) f h
    with (a f h)
  ...  | timeout = timeout
  ...  | nullpointer = nullpointer
  ...  | ok (Σ , h' , v , ext)
       with (b v (wk ext f) h')
  ...     | timeout = timeout
  ...     | nullpointer = nullpointer
  ...     | ok (Σ' , h'' , v' , ext') = ok (Σ' , h'' , v' , ext ⊚ ext')

  return     :  ∀ {s Σ}{p : List Scope → Set} → p Σ → M s p Σ
  return v f h = ok (_ , h , v , ⊑-refl)

  getFrame   :  ∀ {s Σ} → M s (Frame s) Σ
  getFrame f = return f f

  usingFrame  :  ∀ {s s' Σ}{p : List Scope → Set} → Frame s Σ → M s p Σ → M s' p Σ
  usingFrame f a _ = a f

  timeoutᴹ    :  ∀ {s Σ}{p : List Scope → Set} → M s p Σ
  timeoutᴹ _ _ = timeout

  raise : ∀ {s Σ}{p : List Scope → Set} → M s p Σ
  raise _ _ = nullpointer

  init      :  ∀ {Σ s' ds es} → (s : Scope) → ⦃ shape : g s ≡ (ds , es) ⦄ →
               Slots ds Σ → Links es Σ → M s' (Frame s) Σ
  init {Σ} s slots links _ h
    with (initFrame s slots links h)
  ...  | (f' , h') = ok (_ , h' , f' , ∷ʳ-⊒ s Σ)

  getv       :  ∀ {s t Σ} → (s ↦ t) → M s (Valᵗ t) Σ
  getv p f h = return (getVal f p h) f h

  getf  :  ∀ {s s' Σ} → (s ⟶ s')  → M s (Frame s') Σ
  getf p f h = return (getFrame' f p h) f h

  getd  :  ∀ {s t Σ} → t ∈ declsOf s → M s (Valᵗ t) Σ
  getd d f h = return (getSlot f d h) f h

  setd  :  ∀ {s t Σ} → t ∈ declsOf s → Valᵗ t Σ → M s (λ _ → ⊤) Σ
  setd d v f h with (setSlot f d v h)
  ...             | h' = return tt f h'

  setv  :  ∀ {s t Σ} → (s ↦ t) → Valᵗ t Σ → M s (λ _ → ⊤) Σ
  setv p v f h with (setVal f p v h)
  ...             | h' = return tt f h'

  _^_  :  ∀ {Σ Γ}{p q : List Scope → Set} ⦃ w : Weakenable q ⦄ →
          M Γ p Σ → q Σ → M Γ (p ⊗ q) Σ
  (a ^ x) f h
    with (a f h)
  ...  | timeout = timeout
  ...  | nullpointer = nullpointer
  ...  | ok (Σ , h' , v , ext) = ok (Σ , h' , (v , wk ext x) , ext)


  -------------------------------------------------
  -- MONADIC LIFTINGS FOR UPCASTING AND COERCION --
  -------------------------------------------------
  
  upᴹⱽ : ∀ {t t' s Σ} → t <: t' → M s (Val t) Σ → M s (Val<: t') Σ
  upᴹⱽ σ m f h
    with (m f h)
  ...  | timeout = timeout
  ...  | nullpointer = nullpointer
  ...  | ok (Σ , h' , v , ext) = ok (Σ , h' , upcast σ v , ext)

  upᴹ : ∀ {t t' s Σ} → t <: t' → M s (Val<: t) Σ → M s (Val<: t') Σ
  upᴹ σ m f h
    with (m f h)
  ...  | timeout = timeout
  ...  | nullpointer = nullpointer
  ...  | ok (Σ , h' , upcast σ' v , ext) = ok (Σ , h' , upcast (<:-trans σ' σ) v , ext)

  coerceᴹ :  ∀ {t s Σ} → M s (Val<: t) Σ → M s (Val t) Σ
  coerceᴹ m f h
    with (m f h)
  ...  | timeout = timeout
  ...  | nullpointer = nullpointer
  ...  | ok (Σ , h' , upcast σ v , ext) = ok (Σ , h' , coerce<: σ v h' , ext)

  coerceⱽ :  ∀ {t s Σ} → Val<: t Σ → M s (Val t) Σ
  coerceⱽ (upcast σ v) f h = return (coerce<: σ v h) f h


  --------------
  -- DEFAULTS --
  --------------

  default : {Σ : List Scope} → (t : VTy) → Val t Σ
  default int     = num (ℤ.pos 0)
  default (ref s) = null
  default void    = void

  default<: : {Σ : List Scope} → (t : VTy) → Val<: t Σ
  default<: t = upcast refl (default t)

  defaults : ∀ {fs : List Ty}{Σ} → All (#v (λ _ → ⊤)) fs → Slots fs Σ
  defaults {[]}          []           = []
  defaults {vᵗ t ∷ fs} (#v' _ ∷ ts) = vᵗ (reflv (default t)) ∷ defaults {fs} ts

  mutual
    eval<:  :  ℕ → ∀ {t s Σ} → Expr<: s t → M s (Val<: t) Σ
    eval    :  ℕ → ∀ {t s Σ} → Expr s t → M s (Val<: t) Σ

    eval<: k (upcast σ e) = upᴹ σ (eval k e)

    -- coerces to val
    evalᶜ : ℕ → ∀ {t s Σ} → Expr<: s t → M s (Val t) Σ
    evalᶜ k e = coerceᴹ (eval<: k e)

    eval zero _ = timeoutᴹ
    eval (suc k) (num x) = return (reflv (num x))
    eval (suc k) (iop x l r) = evalᶜ k l >>= λ{ (num il) →
                               evalᶜ k r >>= λ{ (num ir) →
                               return (reflv (num (il + ir))) }}
    eval (suc k) null = return (reflv null)
    eval (suc k) (var x)          =  getv x >>= λ{ (vᵗ v) → return v }
    eval (suc k) (new x)          =  getv x >>= λ{ (cᵗ class f) →
                                     usingFrame f (init-obj k class) >>= λ{ f' →
                                     return (reflv (ref f')) }}
    eval (suc k) (get e p)        =  evalᶜ k e >>= λ{ null → raise ; (ref f) →
                                     usingFrame f (getv p) >>= λ{ (vᵗ v) →
                                     return v }}
    eval (suc k) (call e p args)  =  eval<: k e >>= λ v →
                                     (coerceⱽ v ^ v) >>= λ{ (null , _) → raise ; (ref f , v) →
                                     (usingFrame f (getv p) ^ (v ′ f))
                                      >>= λ{ (mᵗ (meth s ⦃ shape ⦄ b) , v , f) →
                                     (eval-args k args ^ (v ′ f)) >>= λ{ (slots , v , f) →
                                     init s ⦃ shape ⦄ (vᵗ v ∷ slots) (f ∷ []) >>= λ f' →
                                     usingFrame f' (eval-body k b) }}}
  
    eval-args : ℕ → ∀ {s ts Σ} → All (Expr<: s) ts → M s (Slots (Data.List.Most.map vᵗ ts)) Σ
    eval-args zero _ = timeoutᴹ
    eval-args (suc k) [] = return []
    eval-args (suc k) (e ∷ es) = eval<: k e >>= λ v →
                                 (eval-args k es ^ v) >>= λ{ (slots , v) →
                                 return (vᵗ v ∷ slots) }

    eval-stmt : ℕ → ∀ {s s' Σ} → Stmt s s' → M s (Frame s') Σ
    eval-stmt zero _ = timeoutᴹ
    eval-stmt (suc k) (loc s t) = getFrame >>= λ f → init s (vᵗ (default<: t) ∷ []) (f ∷ [])
    eval-stmt (suc k) (asgn x e) = eval<: k e >>= λ{ v →
                                   setv x (vᵗ v) >>= λ _ → getFrame }
    eval-stmt (suc k) (set e x e') = evalᶜ k e >>= λ{ (ref f) →
                                     (eval<: k e' ^ f) >>= λ{ (v , f) →
                                     usingFrame f (setv x (vᵗ v)) >>= λ _ → getFrame }
                                   ; null → raise }
    eval-stmt (suc k) (do e) = eval<: k e >>= λ _ → getFrame

    eval-stmts : ℕ → ∀ {s s' Σ} → Stmts s s' → M s (Frame s') Σ
    eval-stmts zero _ = timeoutᴹ
    eval-stmts (suc k) ε = getFrame
    eval-stmts (suc k) (stmt ◅ stmts) = eval-stmt k stmt >>= λ f' →
                                        usingFrame f' (eval-stmts k stmts)

    eval-body : ℕ → ∀ {s t Σ} → Body s t → M s (Val<: t) Σ
    eval-body zero _ = timeoutᴹ
    eval-body (suc k) (body stmts e) = eval-stmts k stmts >>= λ f →
                                       usingFrame f (eval<: k e)
    eval-body (suc k) (body-void stmts) = eval-stmts k stmts >>= λ f →
                                          return (reflv void)

    init-obj : ℕ → ∀ {sʳ s Σ} → Class sʳ s → M sʳ (Frame s) Σ
    init-obj zero _ = timeoutᴹ
    init-obj (suc k) (class0 ⦃ shape ⦄ ms fs oms)
      = getFrame >>= λ f →
        init _ ⦃ shape ⦄ (slotify ms ++-all defaults fs) (f ∷ []) >>= λ f' →
        (usingFrame f' (override oms) ^ f') >>= λ{ (_ , f') → return f' }
    init-obj (suc k) (class1 p ⦃ shape ⦄ ms fs oms)
      = getv p >>= λ{ (cᵗ class' f') →
        (usingFrame f' (init-obj k class') ^ f') >>= λ{ (f , f') →
        init _ ⦃ shape ⦄ (slotify ms ++-all defaults fs) (f' ∷ f ∷ []) >>= λ f'' →
        (usingFrame f'' (override oms) ^ f'') >>= λ{ (_ , f'') → return f'' }}}

    slotify : ∀ {ms s Σ} → All (#m (Meth s)) ms → Slots ms Σ
    slotify {[]}            []           = []
    slotify {mᵗ ts rt ∷ mts} (#m' m ∷ ms) = mᵗ m ∷ slotify {mts} ms
    
    override : ∀ {s Σ}{oms : List (List VTy × VTy)} → 
               All (λ x → (s ↦ (mᵗ (proj₁ x) (proj₂ x))) × Meth s (proj₁ x) (proj₂ x)) oms →
               M s (λ _ → ⊤) Σ
    override [] = return tt
    override ((p , m) ∷ oms) = setv p (mᵗ m) >>= λ _ →
                               override oms

