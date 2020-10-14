module Data.List.All.Properties.Extra {a}{A : Set a} where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Fin
open import Data.List as List hiding (reverse)
open import Data.List.Relation.Unary.Any hiding (tail)
open import Data.List.Membership.Propositional
open import Data.List.Properties.Extra
open import Data.List.At
open import Data.List.Relation.Unary.All as All hiding (_[_]=_)
open import Data.List.Relation.Unary.All.Properties
open import Data.Product
open import Function

map-map : ∀ {p q r}{P : A → Set p}{Q : A → Set q}{R : A → Set r}{l : List A}(ps : All P l)
          {f : ∀ {x : A} → P x → Q x}{g : ∀ {x : A} → Q x → R x} →
          All.map g (All.map f ps) ≡ All.map (g ∘ f) ps
map-map [] = refl
map-map (px ∷ ps) = cong₂ _∷_ refl (map-map ps)

drop-all : ∀ {p}{P : A → Set p}{l : List A} n → All P l → All P (drop n l)
drop-all zero px = px
drop-all (suc n) [] = []
drop-all (suc n) (px ∷ pxs) = drop-all n pxs

split-++ : ∀ {p}{P : A → Set p}(l m : List A) → All P (l ++ m) → All P l × All P m
split-++ [] m pxs = [] , pxs
split-++ (x ∷ l) m (px ∷ pxs) with split-++ l m pxs
... | lp , rp = px ∷ lp , rp

_++-all_ : ∀ {l m p}{P : A → Set p} → All P l → All P m → All P (l ++ m)
[] ++-all pm = pm
(px ∷ pl) ++-all pm = px ∷ (pl ++-all pm)

∈-all : ∀ {p}{P : A → Set p}{l : List A}{x} → x ∈ l → All P l → P x
∈-all (here refl) (px ∷ q) = px
∈-all (there p) (px ∷ q) = ∈-all p q

-- proof matters; update a particular witness of a property
_All[_]≔_ : ∀ {p}{P : A → Set p} {xs : List A} {i x} →
            All P xs → xs [ i ]= x → P x → All P xs
_All[_]≔_ [] ()
_All[_]≔_ {xs = .(_ ∷ _)} {zero} (px ∷ xs) refl px' = px' ∷ xs
_All[_]≔_ {xs = .(_ ∷ _)} {suc i} (px ∷ xs) q px' = px ∷ (xs All[ q ]≔ px')

-- strong update
-- _All[_]≔!_ : ∀ {p}{P : A → Set p} {xs : List A} {x} →
--             All P xs → (i : Fin (length xs)) → P x → All P (xs [ i ]≔ x)
-- [] All[ () ]≔! y
-- (px ∷ xs) All[ zero ]≔! y = y ∷ xs
-- (px ∷ xs) All[ suc i ]≔! y = px ∷ xs All[ i ]≔! y

_all-∷ʳ_ : ∀ {p}{l : List A} {x} {P : A → Set p} → All P l → P x → All P (l ∷ʳ x)
_all-∷ʳ_ [] q = q ∷ []
_all-∷ʳ_ (px ∷ p) q = px ∷ (p all-∷ʳ q)

-- All≔'∘map : ∀ {p q}{P : A → Set p}{Q : A → Set q}{xs : List A} {x}(pxs : All P xs)(e : x ∈ xs)(px : P x)(f : ∀ {x} → P x → Q x) →
--             (All.map f pxs) All[ e ]≔' (f px) ≡ All.map f (pxs All[ e ]≔' px)
-- All≔'∘map [] ()
-- All≔'∘map (px ∷ pxs) (here refl) qx f = refl
-- All≔'∘map (px ∷ pxs) (there e) qx f = cong₂ _∷_ refl (All≔'∘map pxs e qx f)

all-∷ʳ∘map : ∀ {p q}{P : A → Set p}{Q : A → Set q}{xs : List A} {x}(pxs : All P xs)(px : P x)(f : ∀ {x} → P x → Q x) →
             (All.map f pxs) all-∷ʳ (f px) ≡ All.map f (pxs all-∷ʳ px)
all-∷ʳ∘map [] px f = refl
all-∷ʳ∘map (px₁ ∷ pxs) px f = cong₂ _∷_ refl (all-∷ʳ∘map pxs px f)

lookup∘map : ∀ {p q}{P : A → Set p}{Q : A → Set q}{xs : List A} {x}(pxs : All P xs)(e : x ∈ xs)(f : ∀ {x} → P x → Q x) →
             All.lookup (All.map f pxs) e ≡ f (All.lookup pxs e)
lookup∘map [] ()
lookup∘map (px ∷ pxs) (here refl) f = refl
lookup∘map (px ∷ pxs) (there e) f = lookup∘map pxs e f

erase : ∀ {p b}{P : A → Set p}{l : List A}{B : Set b} → (∀ {x} → P x → B) → All P l → List B
erase f [] = []
erase f (px ∷ xs₁) = f px ∷ erase f xs₁

-- pop₁ : ∀ {x : A}{p xs}{P : A → Set p} → All P (x ∷ xs) → P x × All P xs
-- pop₁ st = head st , tail st

-- open import Data.List.Properties
-- popₙ : ∀ (as : List A){p xs}{P : A → Set p} → All P (as ++ xs) → All P (List.reverse as) × All P xs
-- popₙ [] st = [] , st
-- popₙ (x ∷ xs) (px ∷ pxs) rewrite unfold-reverse x xs =
--   let pys , pzs = popₙ xs pxs in (pys all-∷ʳ px) , pzs

-- open import Relation.Binary.Core
-- open import Data.List.Relation.Pointwise hiding (Rel)
-- module _ {a ℓ}{A : Set a}(_∼_ : Rel A ℓ) where

--   pw-map : ∀ {l m p}{P : A → Set p} → (∀ {a b} → a ∼ b → P a → P b) → Pointwise _∼_ l m → All P l → All P m
--   pw-map f [] [] = []
--   pw-map f (x∼y ∷ r) (px ∷ xs) = f x∼y px ∷ pw-map f r xs
