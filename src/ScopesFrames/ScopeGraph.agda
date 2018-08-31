open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin
open import Data.List hiding (concat)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List.Membership.Propositional
open import Data.List.Any hiding (map)
open import Data.Vec as Vec using (Vec)
open import Data.Product hiding (map)
open import Data.Unit

module ScopesFrames.ScopeGraph (Ty : ℕ → Set)
                               (Name : Set)
                               (Label : Set)where

  Scope : ℕ → Set
  Scope k = Fin k

  Decls : ℕ → Set -- not actually dependent on n [for now]
  Decls k = List (Name × Ty k)

  Edges : ℕ → Set
  Edges k = List (Label × Scope k)

  Node : ℕ → Set
  Node k = Decls k × Edges k

  record Graph : Set where
    constructor mkGraph
    field
      ı     : ℕ
      graph : Vec (Node ı) ı

  open Graph

  -- Some projection functions:
  declsOf : (g : Graph) → Scope (ı g) → List (Name × Ty (ı g))
  declsOf g s = proj₁ (Vec.lookup s (graph g))

  declsOf♭ : (g : Graph) → Scope (ı g) → List (Ty (ı g))
  declsOf♭ g s = map proj₂ (proj₁ (Vec.lookup s (graph g)))

  edgesOf : (g : Graph) → Scope (ı g) → List (Label × Scope (ı g))
  edgesOf g s  = proj₂ (Vec.lookup s (graph g))

  edgesOf♭ : (g : Graph) → Scope (ı g) → List (Scope (ı g))
  edgesOf♭ g s  = map proj₂ (proj₂ (Vec.lookup s (graph g)))

  nodeOf : (g : Graph) → Scope (ı g) → Node (ı g)
  nodeOf g s = Vec.lookup s (graph g)

  nodeOf♭ : (g : Graph) → Scope (ı g) → List (Ty (ı g)) × List (Scope (ı g))
  nodeOf♭ g s = let node = Vec.lookup s (graph g) in
                map proj₂ (proj₁ node) , map proj₂ (proj₂ node)

  convert-shape♭ : {g : Graph} {s : Scope (ı g)} {ds : Decls (ı g)} {es : Edges (ı g)} →
                   nodeOf g s ≡ (ds , es) →
                   nodeOf♭ g s ≡ (map proj₂ ds , map proj₂ es)
  convert-shape♭ shape rewrite shape = refl

  -- A resolution path is a witness that we can traverse a sequence of
  -- scope edges (`_⟶_`) in `g` to arrive at a declaration of type
  -- `t`:

  data _⊢_⟶_ (g : Graph) : Scope (ı g) → Scope (ı g) → Set where
    []   :  ∀ {s} → g ⊢ s ⟶ s
    _∷_  :  ∀ {l} {s s' s''} → (l , s') ∈ edgesOf g s → g ⊢ s' ⟶ s'' → g ⊢ s ⟶ s''

  data _⊢♭_⟶_ (g : Graph) : Scope (ı g) → Scope (ı g) → Set where
    []   :  ∀ {s} → g ⊢♭ s ⟶ s
    _∷_  :  ∀ {s s' s''} → s' ∈ edgesOf♭ g s → g ⊢♭ s' ⟶ s'' → g ⊢♭ s ⟶ s''

  convert-path♭ : {g : Graph} {s s' : Scope (ı g)} →
                  g ⊢  s ⟶ s' →
                  g ⊢♭ s ⟶ s'
  convert-path♭ [] = []
  convert-path♭ (x ∷ p) = ∈♭ x ∷ convert-path♭ p
    where
      ∈♭ : {A B : Set} {a : A} {b : B} {xs : List (A × B)} →
           (a , b) ∈ xs →
           b ∈ map proj₂ xs
      ∈♭ (here refl) = here refl
      ∈♭ (there p) = there (∈♭ p)
      

  -- path concatenation
  concat : {g : Graph}{s s' s'' : Scope (ı g)}
           (p1 : g ⊢ s ⟶ s') (p2 : g ⊢ s' ⟶ s'') →
           g ⊢ s ⟶ s''
  concat [] p₂ = p₂
  concat (x ∷ p₁) p₂ = x ∷ (concat p₁ p₂)

  concat♭ : {g : Graph}{s s' s'' : Scope (ı g)}
              (p1 : g ⊢♭ s ⟶ s') (p2 : g ⊢♭ s' ⟶ s'') →
              g ⊢♭ s ⟶ s''
  concat♭ [] p₂ = p₂
  concat♭ (x ∷ p₁) p₂ = x ∷ (concat♭ p₁ p₂)

  data _⊢_↦_ (g : Graph) (s : Scope (ı g)) (t : Ty (ı g)) : Set where
    path : ∀ {x : Name} {s'} → g ⊢ s ⟶ s' → (x , t) ∈ declsOf g s' → g ⊢ s ↦ t

  data _⊢♭_↦_ (g : Graph) (s : Scope (ı g)) (t : Ty (ı g)) : Set where
    path♭ : ∀ {s'} → g ⊢♭ s ⟶ s' → t ∈ declsOf♭ g s' → g ⊢♭ s ↦ t

  prepend : {g : Graph} {s s' : Scope (ı g)} {t : Ty (ı g)}
            (p : g ⊢ s ⟶ s') (q : g ⊢ s' ↦ t) →
            g ⊢ s ↦ t
  prepend p (path p' d) = path (concat p p') d

  prepend♭ : {g : Graph} {s s' : Scope (ı g)} {t : Ty (ı g)}
             (p : g ⊢♭ s ⟶ s') (q : g ⊢♭ s' ↦ t) →
             g ⊢♭ s ↦ t
  prepend♭ p (path♭ p' d) = path♭ (concat♭ p p') d
