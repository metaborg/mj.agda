open import Data.Nat renaming (_≟_ to _Nat=_)
open import Data.Nat.Properties
open import Data.List using (List; []; _∷_; foldr)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List.Membership.Propositional
open import Data.List.Any hiding (map)
open import Data.List.All using (All; lookup)
open import Data.Vec as Vec using (Vec)
open import Data.Product hiding (map)
open import Data.Bool
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.Core


module ScopesFrames.ScopeGraph (Ty : Set)
                               (Name : Set)
                               (Label : Set)where

  -- Decls : ℕ → Set -- not actually dependent on n [for now]
  -- Decls k = List (Name × Ty k)

  -- Edges : ℕ → Set
  -- Edges k = List (Label × Scope k)

  -- Node : ℕ → Set
  -- Node k = Decls k × Edges k

  record Graph : Set where
    constructor mkGraph
    field
      ı     : ℕ
      decls : List (ℕ × Name × Ty)
      edges : List (ℕ × Label × ℕ)

      wf :
        All (λ x → proj₁ x ≤ ı) decls
        × All (λ x → proj₁ x ≤ ı × proj₂ (proj₂ x) ≤ ı) edges

  open Graph

  Scope : Set
  Scope = ℕ

  --------------------------
  -- PROJECTION FUNCTIONS --
  --------------------------

  -- More informative fold function
  foldr' : ∀ {a b} {A : Set a} {B : Set b} → (l : List A) → ((a : A) → a ∈ l → B → B) → B → B
  foldr' [] c n       = n
  foldr' (x ∷ xs) c n = c x (here refl) (foldr' xs (λ a w b → c a (there w) b) n)


  declsOf : (g : Graph) → Scope → List (Name × Ty)
  declsOf g s =
    foldr (λ where
             (x , name , ty) rs →
               if ⌊ x Nat= s ⌋ then (name , ty) ∷ rs else rs)
          []
          (decls g)

  -- Convert an edge pointer to a scope
  scopify : {l : Label} {n m : ℕ} (g : Graph) (edge : (n , l , m) ∈ edges g) →
            m ≤ ı g
  scopify g edge = proj₂ (lookup (proj₂ (wf g)) edge)

  edgesOf : (g : Graph) → Scope → List (Label × ℕ)
  edgesOf g s =
    foldr (λ where
             (x , lbl , y) rs →
               if ⌊ x Nat= s ⌋ then (lbl , y) ∷ rs else rs)
          []
          (edges g)

  -- Projection lemmas
  dec-refl : ∀ m → ⌊ m Nat= m ⌋ ≡ true
  dec-refl zero = refl
  dec-refl (suc m) with (m Nat= m)
  dec-refl (suc m)    | yes refl = refl
  dec-refl (suc m)    | no f with f refl
  ...                           | ()

  lem₁ : {X Y : Set} (zs : List (ℕ × X × Y))
         (m : ℕ) {x : X} {y : Y}
         (z : (m , x , y) ∈ zs) →
         (x , y) ∈ foldr (λ where
                            (s , x , y) rs →
                              if ⌊ s Nat= m ⌋ then (x , y) ∷ rs else rs)
                         []
                         zs
  lem₁ [] m ()
  lem₁ (.(m , _ , _) ∷ zs) m (here refl) rewrite (dec-refl m) = here refl
  lem₁ ((n , _ , _) ∷ zs)  m (there z) with (n Nat= m)
  ...                                     | yes refl = there (lem₁ zs m z)
  ...                                     | no f = lem₁ zs m z

  lem₂ : {X Y : Set} (zs : List (ℕ × X × Y))
         (m : ℕ) {x : X} {y : Y}
         (zs' : (x , y) ∈ foldr (λ where
                                      (s , x , y) rs →
                                        if ⌊ s Nat= m ⌋ then (x , y) ∷ rs else rs)
                                   []
                                   zs) →
         (m , x , y) ∈ zs
  lem₂ [] m ()
  lem₂ ((n , x , t) ∷ zs) m z with (n Nat= m)
  lem₂ ((n , x , t) ∷ zs) .n (here refl) | yes refl = here refl
  lem₂ ((n , x , t) ∷ zs) .n (there z)   | yes refl = there (lem₂ zs n z)
  ...                                    | no f     = there (lem₂ zs m z)

  decl-to-declsOf : {g : Graph} {s : Scope} {x : Name} {t : Ty} →
                    (s , x , t) ∈ decls g →
                    (x , t) ∈ declsOf g s
  decl-to-declsOf {mkGraph _ decls _ _} {m} d = lem₁ decls m d

  declsOf-to-decl : {g : Graph} {s : Scope} {x : Name} {t : Ty} →
                    (x , t) ∈ declsOf g s →
                    (s , x , t) ∈ decls g
  declsOf-to-decl {mkGraph _ decls _ _} {m} ds = lem₂ decls m ds

  edge-to-edgesOf : {g : Graph} {s : Scope} {l : Label} {n : ℕ} →
                    (s , l , n) ∈ edges g →
                    (l , n) ∈ edgesOf g s
  edge-to-edgesOf {mkGraph _ _ edges _} {m} d = lem₁ edges m d

  edgesOf-to-edge : {g : Graph} {s : Scope} {l : Label} {n : ℕ} →
                    (l , n) ∈ edgesOf g s →
                    (s , l , n) ∈ edges g
  edgesOf-to-edge {mkGraph _ _ edges _} {m} es = lem₂ edges m es

  -- FIXME: corresponding lemma for semantic edge projection

  -- edgesOf : (g : Graph) → Scope (ı g) → List (Label × Scope (ı g))
  -- edgesOf g s  = proj₂ (Vec.lookup s (graph g))

  -- edgesOf♭ : (g : Graph) → Scope (ı g) → List (Scope (ı g))
  -- edgesOf♭ g s  = map proj₂ (proj₂ (Vec.lookup s (graph g)))

  shapeOf : (g : Graph) → Scope → List (Name × Ty) × List (Label × ℕ)
  shapeOf g s = declsOf g s , edgesOf g s

  -- nodeOf♭ : (g : Graph) → Scope (ı g) → List (Ty (ı g)) × List (Scope (ı g))
  -- nodeOf♭ g s = let node = Vec.lookup s (graph g) in
  --               map proj₂ (proj₁ node) , map proj₂ (proj₂ node)

  -- convert-shape♭ : {g : Graph} {ds : Decls (ı g)} {es : Edges (ı g)}
  --                  (s : Scope (ı g)) →
  --                  nodeOf g s ≡ (ds , es) →
  --                  nodeOf♭ g s ≡ (map proj₂ ds , map proj₂ es)
  -- convert-shape♭ s shape rewrite shape = refl

  -- A resolution path is a witness that we can traverse a sequence of
  -- scope edges (`_⟶_`) in `g` to arrive at a declaration of type
  -- `t`:

  data _⊢_⟶_ (g : Graph) : ℕ → ℕ → Set where
    []   :  ∀ {s} → g ⊢ s ⟶ s
    _∷_  :  ∀ {l} {s s' s''} → (s , l , s') ∈ edges g → g ⊢ s' ⟶ s'' → g ⊢ s ⟶ s''

  -- data _⊢♭_⟶_ (g : Graph) : Scope (ı g) → Scope (ı g) → Set where
  --   []   :  ∀ {s} → g ⊢♭ s ⟶ s
  --   _∷_  :  ∀ {s s' s''} → s' ∈ edgesOf♭ g s → g ⊢♭ s' ⟶ s'' → g ⊢♭ s ⟶ s''

  -- convert-_∈_♭ : {A B : Set} {a : A} {b : B} {xs : List (A × B)} →
  --                (a , b) ∈ xs →
  --                b ∈ map proj₂ xs
  -- convert-_∈_♭ (here refl) = here refl
  -- convert-_∈_♭ (there p) = there (convert-_∈_♭ p)


  -- convert-reach♭ : {g : Graph} {s s' : Scope (ı g)} →
  --                  g ⊢  s ⟶ s' →
  --                  g ⊢♭ s ⟶ s'
  -- convert-reach♭ [] = []
  -- convert-reach♭ (x ∷ p) = convert-_∈_♭ x ∷ convert-reach♭ p

  -- path concatenation
  concat : {g : Graph}{s s' s'' : ℕ}
           (p1 : g ⊢ s ⟶ s') (p2 : g ⊢ s' ⟶ s'') →
           g ⊢ s ⟶ s''
  concat [] p₂ = p₂
  concat (x ∷ p₁) p₂ = x ∷ (concat p₁ p₂)

  -- concat♭ : {g : Graph}{s s' s'' : Scope (ı g)}
  --           (p1 : g ⊢♭ s ⟶ s') (p2 : g ⊢♭ s' ⟶ s'') →
  --           g ⊢♭ s ⟶ s''
  -- concat♭ [] p₂ = p₂
  -- concat♭ (x ∷ p₁) p₂ = x ∷ (concat♭ p₁ p₂)

  data _⊢_↦_ (g : Graph) (s : ℕ) (t : Ty) : Set where
    path : ∀ {x : Name} {s'} → g ⊢ s ⟶ s' → (s' , x , t) ∈ decls g → g ⊢ s ↦ t

  -- data _⊢♭_↦_ (g : Graph) (s : Scope (ı g)) (t : Ty (ı g)) : Set where
  --   path♭ : ∀ {s'} → g ⊢♭ s ⟶ s' → t ∈ declsOf♭ g s' → g ⊢♭ s ↦ t

  -- convert-path♭ : {g : Graph} {s : Scope (ı g)} {t : Ty (ı g)} →
  --                 g ⊢  s ↦ t →
  --                 g ⊢♭ s ↦ t
  -- convert-path♭ (path r d) =
  --   path♭ (convert-reach♭ r) (convert-_∈_♭ d)

  prepend : {g : Graph} {s s' : ℕ} {t : Ty}
            (p : g ⊢ s ⟶ s') (q : g ⊢ s' ↦ t) →
            g ⊢ s ↦ t
  prepend p (path p' d) = path (concat p p') d

  -- prepend♭ : {g : Graph} {s s' : Scope (ı g)} {t : Ty (ı g)}
  --            (p : g ⊢♭ s ⟶ s') (q : g ⊢♭ s' ↦ t) →
  --            g ⊢♭ s ↦ t
  -- prepend♭ p (path♭ p' d) = path♭ (concat♭ p p') d
