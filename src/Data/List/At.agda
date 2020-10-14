module Data.List.At where

open import Data.Nat
open import Data.List
open import Data.List.Relation.Unary.All hiding (map; lookup; _[_]=_)
open import Data.List.Relation.Unary.Any hiding (map; lookup)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Binary.Pointwise hiding (refl; map)
open import Data.Fin hiding (_<_)
open import Data.Maybe hiding (map)
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

maybe-lookup : ∀ {a}{A : Set a} → ℕ → List A → Maybe A
maybe-lookup n [] = nothing
maybe-lookup zero (x ∷ μ) = just x
maybe-lookup (suc n) (x ∷ μ) = maybe-lookup n μ

maybe-write : ∀ {a}{A : Set a} → ℕ → A →  List A → Maybe (List A)
maybe-write n _ [] = nothing
maybe-write zero v (x ∷ z) = just (v ∷ z)
maybe-write (suc n) v (x ∷ z) = maybe-write n v z

_[_]=_ : ∀ {a}{A : Set a} → List A → ℕ → A → Set _
l [ i ]= x = maybe-lookup i l ≡ just x

[]=-map : ∀ {a b}{A : Set a}{B : Set b}{x} i → (l : List A) →
                   l [ i ]= x → ∀ (f : A → B) → (map f l) [ i ]= (f x)
[]=-map _ [] ()
[]=-map zero (x ∷ l) refl = λ f → refl
[]=-map (suc i) (x ∷ l) p = []=-map i l p

at-lookup : ∀ {a}{A : Set a} → (l : List A) → (i : Fin (length l)) → l [ toℕ i ]= (lookup l i)
at-lookup [] ()
at-lookup (x ∷ l) zero = refl
at-lookup (x ∷ l) (suc i) = at-lookup l i

lookup-in : ∀ {a}{A : Set a} → (l : List A) → (i : Fin (length l)) → (lookup l i) ∈ l
lookup-in [] ()
lookup-in (x ∷ l) zero = here refl
lookup-in (x ∷ l) (suc i) = there (lookup-in l i)

dec-lookup : ∀ {a} {A : Set a} → (i : ℕ) → (l : List A) → Dec (∃ λ x → l [ i ]= x)
dec-lookup _ [] = no (λ{ (_ , ())})
dec-lookup zero (x ∷ l) = yes (x , refl)
dec-lookup (suc i) (_ ∷ l) = dec-lookup i l

all-lookup : ∀ {a} {A : Set a} {l : List A} {i x p P} → l [ i ]= x → All {p = p} P l → P x
all-lookup {l = []} () q
all-lookup {l = x ∷ l} {zero} refl (px ∷ q) = px
all-lookup {l = x ∷ l} {suc i} p (px ∷ q) = all-lookup p q

[]=-length : ∀ {a} {A : Set a} (L : List A) {i x} → L [ i ]= x → i < length L
[]=-length [] ()
[]=-length (x ∷ L) {zero} refl = s≤s z≤n
[]=-length (x ∷ L) {suc i} p = s≤s ([]=-length L p)

∷ʳ[length] : ∀ {a} {A : Set a} (l : List A) x → (l ∷ʳ x) [ length l ]= x
∷ʳ[length] [] y = refl
∷ʳ[length] (x ∷ Σ) y = ∷ʳ[length] Σ y

pointwise-lookup : ∀ {a b ℓ A B P l m i x} → Pointwise {a} {b} {ℓ} {A} {B} P l m →
                    l [ i ]= x → ∃ λ y → m [ i ]= y × P x y
pointwise-lookup [] ()
pointwise-lookup {i = zero} (x∼y ∷ q) refl = _ , refl , x∼y
pointwise-lookup {i = suc i} (x∼y ∷ q) p = pointwise-lookup q p

pointwise-lookup′ : ∀ {a b ℓ A B P l m i x y} → Pointwise {a} {b} {ℓ} {A} {B} P l m →
                    l [ i ]= x → m [ i ]= y → P x y
pointwise-lookup′ [] () q
pointwise-lookup′ {i = zero} (x∼y ∷ z) refl refl = x∼y
pointwise-lookup′ {i = suc i} (x∼y ∷ z) p q = pointwise-lookup′ z p q
