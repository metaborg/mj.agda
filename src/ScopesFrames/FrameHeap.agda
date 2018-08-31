open import Data.Nat
open import Data.Fin
open import Data.List.Most
open import Data.List.All renaming (lookup to lookup∀)
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Data.Unit
open import Data.List.Prefix
open import Data.List.Properties.Extra
open import Data.List.All.Properties.Extra
open import Data.List.All as List∀ hiding (lookup)
open import Data.Maybe hiding (All)
open import Agda.Primitive

module ScopesFrames.FrameHeap (Ty : ℕ → Set)
                              (Name : Set)
                              (Label : Set) where

open import ScopesFrames.ScopeGraph Ty Name Label

open Graph

module UsesGraph {g : Graph} where

  open import Relation.Unary.Weakening.ListPrefix

  ----------------------
  -- FRAMES AND HEAPS --
  ----------------------

  -- Heap types summarize what the scope is for each frame location in
  -- the heap:

  HeapTy = List (Scope (ı g))

  -- A frame pointer `Frame s Σ` is a witness that there is a frame
  -- location scoped by `s` in a heap typed by `Σ`:

  Frame : Scope (ı g) → (Σ : HeapTy) → Set
  Frame s Σ = s ∈ Σ

  -- Concrete frames and heaps store values that are weakened when the
  -- heap is extended.  The following definitions are parameterized by
  -- a language-specific notion of weakenable value.

  module UsesVal (Val : Ty (ı g) → HeapTy → Set)
                 (Val-Wk : {t : Ty (ı g)} → Wk (Val t)) where

    -- Slots are given by a list of values that are in one-to-one
    -- correspondence with a list of declarations (types):

    Slots : (ds : List (Ty (ı g))) → (Σ : HeapTy) → Set
    Slots ds Σ = All (λ t → Val t Σ) ds

    -- Links are given by a list of frame pointers (links) that are in
    -- one-to-one correspondence with a list of edges (scopes):

    Links : (es : List (Scope (ı g))) → (Σ : HeapTy) → Set
    Links es Σ = All (λ s → Frame s Σ) es

    -- A heap frame for a scope `s` is given by a set of slots and
    -- links that are in one-to-one correspondence with the
    -- declarations and edges of the scope:

    HeapFrame : Scope (ı g) → HeapTy → Set
    HeapFrame s Σ = Slots (declsOf♭ g s) Σ × Links (edgesOf♭ g s) Σ

    -- A heap typed by `Σ` is given by a list of heap frames such that
    -- each frame location is in the heap is typed by the
    -- corresponding location in `Σ`.

    Heap : (Σ : HeapTy) → Set
    Heap Σ = All (λ s → HeapFrame s Σ) Σ


    ----------------------
    -- FRAME OPERATIONS --
    ----------------------

    -- Frame initialization extends the heap, requiring heap type
    -- weakening.  The `Common.Weakening` module defines a generic
    -- `Weakenable` record, which we instantiate for each entity that
    -- is required to be weakenable.  We use Agda's instance arguments
    -- to automatically resolve the right notion of weakening where
    -- possible.

    -- We add some instances of the Weakenable typeclass
    -- to the instance argument scope:

    instance
      weaken-val' : ∀ {t} → Wk (Val t)
      weaken-val' = Val-Wk

      weaken-heapframe : ∀ {s} → Wk (HeapFrame s)
      weaken-heapframe = record { wk = λ{ ext (slots , links) → (wk ext slots , wk ext links) } }

      weaken-frame : ∀ {s} → Wk (Frame s)
      weaken-frame = record { wk = Wk.wk any-weakenable }

    -- Frame initialization takes as argument:
    --
    -- * a scope `s`;
    --
    -- * a scope shape witness which asserts that looking up `s` in
    --   the current scope graph `g` yields a scope shape where the
    --   declarations are given by a list of types `ds`, and scope
    --   edges are given by a list of scopes `es`;
    --
    -- * a set of slots typed by `ds`;
    --
    -- * a set of links typed by `es`; and
    --
    -- * a heap typed by the heap type `Σ` which also types the slots
    --   and links.
    --
    -- The operation returns an extended heap (`∷ʳ` appends a single
    -- element to a list, and is defined in `Data.List.Base` in the
    -- Agda Standard Library) and a frame pointer into the extended
    -- heap, i.e., the newly allocated and initialized frame.

    initFrame   :  (s : Scope (ı g)) → ∀ {Σ ds es}⦃ shape : nodeOf♭ g s ≡ (ds , es) ⦄ →
                   Slots ds Σ → Links es Σ → Heap Σ → Frame s (Σ ∷ʳ s) × Heap (Σ ∷ʳ s)
    initFrame s {Σ} ⦃ refl ⦄ slots links h =
      let ext = ∷ʳ-⊒ s Σ -- heap extension fact
          f'  = ∈-∷ʳ Σ s -- updated frame pointer witness
          h'  = (wk ⦃ all-weakenable λ x → weaken-heapframe {s = x} ⦄ ext h) all-∷ʳ
                    (wk ⦃ all-weakenable λ x → weaken-val' ⦄ ext slots , wk ext links) -- extended heap
      in (f' , h')

    -- Frames may be self-referential.  For example, the values stored
    -- in the slots of a frame may contain pointers to the frame
    -- itself.  The `initFrame` function above does not support
    -- initializing such self-referential slots, since the slots are
    -- assumed to be typed under the unextended heap.
    --
    -- The `initFrameι` function we now define takes as argument a
    -- function to be used to initialize possibly-self-referential
    -- frame slots.  The function takes as argument a frame pointer
    -- into a heap extended by the scope that we are currently
    -- initializing, and slots are typed under this extended heap;
    -- hence the slots can have self-references to the frame currently
    -- being initialized.

    initFrameι : (s : Scope (ı g)) → ∀ {Σ ds es}⦃ shape : nodeOf♭ g s ≡ (ds , es) ⦄ →
                 (slotsf : Frame s (Σ ∷ʳ s) → Slots ds (Σ ∷ʳ s)) → Links es Σ → Heap Σ →
                 Frame s (Σ ∷ʳ s) × Heap (Σ ∷ʳ s)
    initFrameι s {Σ} ⦃ refl ⦄ slotsf links h =
      let ext = ∷ʳ-⊒ s Σ -- heap extension fact
          f'  = ∈-∷ʳ Σ s -- updated frame pointer witness
          h'  = (wk ⦃ all-weakenable (λ x → weaken-heapframe {s = x}) ⦄ ext h) all-∷ʳ (slotsf f' , wk ext links) -- extended heap
      in (f' , h')


    -- Given a witness that a declaration typed by `t` is in a scope,
    -- and a frame pointer, we can fetch the well-typed value stored
    -- in the corresponding frame slot:

    getSlot : ∀ {s t Σ} → t ∈ declsOf♭ g s → Frame s Σ → Heap Σ → Val t Σ
    getSlot d f h
      with (List∀.lookup h f)
    ...  | (slots , links) = List∀.lookup slots d

    -- Given a witness that a declaration typed by `t` is in a scope,
    -- and a frame pointer, we can mutate the corresponding slot in a
    -- type preserving manner:

    setSlot : ∀ {s t Σ} → t ∈ declsOf♭ g s → Val t Σ → Frame s Σ → Heap Σ → Heap Σ
    setSlot d v f h
      with (List∀.lookup h f)
    ...  | (slots , links) = h All[ f ]≔' (slots All[ d ]≔' v , links)

    -- ... and similarly for edges:

    getLink : ∀ {s s' Σ} → s' ∈ edgesOf♭ g s → Frame s Σ → Heap Σ → Frame s' Σ
    getLink e f h
      with (List∀.lookup h f)
    ...  | (slots , links) = List∀.lookup links e

    setLink : ∀ {s s' Σ} → s' ∈ edgesOf♭ g s → Frame s' Σ → Frame s Σ → Heap Σ → Heap Σ
    setLink e f' f h
      with (List∀.lookup h f)
    ...  | (slots , links) = h All[ f ]≔' (slots , links All[ e ]≔' f')

    -- Given a witness that there is a path through the scope graph
    -- from scope `s` to scope `s'`, a frame typed by `s`, and a
    -- well-typed heap, we can traverse the path by following the
    -- corresponding frame links in the heap to arrive at a frame
    -- scoped by `s'`:

    getFrame : ∀ {s s' Σ} → (g ⊢♭ s ⟶ s') → Frame s Σ → Heap Σ → Frame s' Σ
    getFrame []      f h = f
    getFrame (e ∷ p) f h
      with (List∀.lookup h f)
    ...  | (slots , links) = getFrame p (List∀.lookup links e) h

    -- Given the definitions above, we can define some shorthand
    -- functions for getting and setting values:

    getVal  :  ∀ {s t} → (g ⊢♭ s ↦ t) → ∀ {Σ} → Frame s Σ → Heap Σ → Val t Σ
    getVal (path♭ p d) f h = getSlot d (getFrame p f h) h

    setVal  :  ∀ {s t Σ} → (g ⊢♭ s ↦ t) → Val t Σ → Frame s Σ → Heap Σ → Heap Σ
    setVal (path♭ p d) v f h = setSlot d v (getFrame p f h) h
