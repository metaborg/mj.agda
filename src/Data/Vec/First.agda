module Extensions.VecFirst where

open import Data.Vec
open import Data.Product
open import Level
open import Relation.Nullary
open import Function using (_∘_; _$_)

-- proof that an element is the first in a vector to satisfy the predicate B
data First {a b} {A : Set a} (B : A → Set b) : ∀ {n} (x : A) → Vec A n → Set (a ⊔ b) where

  here  : ∀ {n} {x : A} → (p : B x) → (v : Vec A n) → First B x (x ∷ v)
  there : ∀ {n x} {v : Vec A n} (x' : A) → ¬ (B x') → First B x v → First B x (x' ∷ v)

-- more likable syntax for the above structure
first_∈_⇔_ : ∀ {n} {A : Set} → A → Vec A n → (B : A → Set) → Set 
first_∈_⇔_ x v p = First p x v

-- a decision procedure to find the first element in a vector that satisfies a predicate
find : ∀ {n} {A : Set} (P : A → Set) → ((a : A) → Dec (P a)) → (v : Vec A n) → 
       Dec (∃ λ e → first e ∈ v ⇔ P)
find P dec [] = no (λ{ (e , ()) })
find P dec (x ∷ v) with dec x
find P dec (x ∷ v) | yes px = yes (x , here px v)
find P dec (x ∷ v) | no ¬px with find P dec v
find P dec (x ∷ v) | no ¬px | yes firstv = yes (, there x ¬px (proj₂ firstv))
find P dec (x ∷ v) | no ¬px | no ¬firstv = no $ helper ¬px ¬firstv
  where
    helper : ¬ (P x) → ¬ (∃ λ e → First P e v) → ¬ (∃ λ e → First P e (x ∷ v))
    helper ¬px ¬firstv (.x , here p .v) = ¬px p
    helper ¬px ¬firstv (u  , there ._ _ firstv) = ¬firstv (u , firstv)
