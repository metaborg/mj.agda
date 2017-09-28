open import Data.Nat
open import Data.Fin
open import Data.List.Most
open import Data.List.All renaming (lookup to lookup∀)
open import Data.Vec hiding (_∈_ ; _∷ʳ_ ; _>>=_ ; init)
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Data.Unit
open import Data.List.Prefix
open import Data.List.Properties.Extra
open import Data.List.All.Properties.Extra
open import Data.List.All as List∀ hiding (lookup)
open import Coinduction
open import Data.Maybe hiding (All)
open import Common.Weakening
open import Common.Strength

module ScopeGraph.ScopesFrames (k : ℕ) (Ty : Set) where

Scope = Fin k
Graph = Scope → (List Ty × List Scope)

module UsesGraph (g : Graph) where

  declsOf  :  Scope → List Ty     ;  declsOf s  = proj₁ (g s)
  edgesOf  :  Scope → List Scope  ;  edgesOf s  = proj₂ (g s)

  data _⟶_ : Scope → Scope → Set where
    []   :  ∀ {s} → s ⟶ s
    _∷_  :  ∀ {s s' s''} → s' ∈ edgesOf s → s' ⟶ s'' → s ⟶ s''

  data _↦_ (s : Scope) (t : Ty) : Set where
    path : ∀{s'} → s ⟶ s' → t ∈ declsOf s' → s ↦ t

  [_]≅_ : Scope → List Ty × List Scope → Set
  [ s ]≅ (ds , es) = g s ≡ (ds , es)

  HeapTy = List Scope

  Frame : Scope → (Σ : HeapTy) → Set
  Frame s Σ = s ∈ Σ

  decl : ∀ {ds s es t} → ⦃ shape : g s ≡ (ds , es) ⦄ → t ∈ ds → t ∈ declsOf s
  decl ⦃ refl ⦄ p = p

  module UsesVal (Val : Ty → HeapTy → Set)
                 (weaken-val : ∀ {t Σ Σ'} → Σ ⊑ Σ' → Val t Σ → Val t Σ') where

    instance
      weaken-val' : ∀ {t} → Weakenable (λ Σ → Val t Σ)
      weaken-val' = record { weaken = weaken-val }

    Slots : (ds : List Ty) → (Σ : HeapTy) → Set
    Slots ds Σ = All (λ t → Val t Σ) ds

    Links : (es : List Scope) → (Σ : HeapTy) → Set
    Links es Σ = All (λ s → Frame s Σ) es

    HeapFrame : Scope → HeapTy → Set
    HeapFrame s Σ = Slots (declsOf s) Σ × Links (edgesOf s) Σ

    FrameHeap : (Σ₀ : HeapTy) → (Σ : HeapTy) → Set
    FrameHeap Σ₀ Σ = All (λ s → HeapFrame s Σ₀) Σ

    Heap : (Σ : HeapTy) → Set
    Heap Σ = All (λ s → HeapFrame s Σ) Σ

    open Weakenable ⦃...⦄
    instance
      weaken-slots : ∀ {ts} → Weakenable (Slots ts)
      weaken-slots = record { weaken = weaken ⦃ all-weakenable (λ t → weaken-val' {t}) ⦄ }

      weaken-links : ∀ {es} → Weakenable (Links es)
      weaken-links = record { weaken = weaken ⦃ all-weakenable (λ a → any-weakenable {x = a}) ⦄ }

      weaken-heapframe : ∀ {s} → Weakenable (HeapFrame s)
      weaken-heapframe = record { weaken = λ{ ext (slots , links) → (weaken ext slots , weaken ext links) } }

      weaken-heap : ∀ {Σ'} → Weakenable (λ Σ → FrameHeap Σ Σ')
      weaken-heap = record { weaken = weaken ⦃ all-weakenable (λ s → weaken-heapframe {s = s}) ⦄ }

      weaken-frame : ∀ {s} → Weakenable (Frame s)
      weaken-frame = record { weaken = Weakenable.weaken any-weakenable }

    -- alias
    _⊚_ = ⊑-trans

    -- helper
    pair-eq : ∀ {A B : Set}{x : A × B}{a : A}{b : B} → x ≡ (a , b) → proj₁ x ≡ a × proj₂ x ≡ b
    pair-eq {_} {_} {(p , q)} refl = refl , refl

    initFrame   :  (s : Scope) → ∀ {Σ ds es}⦃ shape : g s ≡ (ds , es) ⦄ →
                   Slots ds Σ → Links es Σ → Heap Σ → Frame s (Σ ∷ʳ s) × Heap (Σ ∷ʳ s)
    initFrame s {Σ} ⦃ refl ⦄ slots links h
        = let ext = ∷ʳ-⊒ s Σ
              f'  = ∈-∷ʳ Σ s
              h'  =
                (weaken ⦃ weaken-heap ⦄ ext h)
                all-∷ʳ
                ((weaken ⦃ weaken-slots ⦄ ext slots , weaken ext links))
          in (f' , h')

    setSlot     :  ∀ {s t Σ} → Frame s Σ → t ∈ declsOf s → Val t Σ → Heap Σ → Heap Σ
    setSlot f d v h
      with (List∀.lookup h f)
    ...  | (slots , links) = h All[ f ]≔' (slots All[ d ]≔' v , links)


    getFrame    :  ∀ {s s' Σ} → Frame s Σ → (s ⟶ s') → Heap Σ → Frame s' Σ
    getFrame f []      h = f
    getFrame f (e ∷ p) h  with (List∀.lookup h f)
    ...                     | (slots , links) = getFrame (List∀.lookup links e) p h

    getSlot     :  ∀ {s t Σ} → Frame s Σ → t ∈ declsOf s → Heap Σ → Val t Σ
    getSlot f d h
      with (List∀.lookup h f)
    ...  | (slots , links) = List∀.lookup slots d

    getVal  :  ∀ {s t Σ} → Frame s Σ → (s ↦ t) → Heap Σ → Val t Σ
    getVal f (path p d) h = getSlot (getFrame f p h) d h

    setVal  :  ∀ {s t Σ} → Frame s Σ → (s ↦ t) → Val t Σ → Heap Σ → Heap Σ
    setVal f (path p d) v h = setSlot (getFrame f p h) d v h
