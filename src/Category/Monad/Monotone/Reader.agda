open import Relation.Binary using (Preorder)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary

module Category.Monad.Monotone.Reader {ℓ}(pre : Preorder ℓ ℓ ℓ) where

open Preorder pre renaming (Carrier to I; _∼_ to _≤_; refl to ≤-refl)

open import Relation.Unary.Monotone pre
open import Relation.Unary.PredicateTransformer using (Pt)
open import Data.Product
open import Function
open import Level hiding (lift)
open import Category.Monad
open import Category.Monad.Monotone.Identity pre
open import Category.Monad.Monotone pre

ReaderT : Pred I ℓ → Pt I ℓ → Pt I ℓ
ReaderT E M P = λ i → E i → M P i

Reader : (Pred I ℓ) → Pt I ℓ
Reader E = ReaderT E Identity

record ReaderMonad E (M : Pred I ℓ → Pt I ℓ) : Set (suc ℓ) where
  field
    ask    : ∀ {i} → M E E i
    reader : ∀ {P} → (E ⇒ P) ⊆ M E P
    local  : ∀ {P E'} → (E ⇒ E') ⊆ (M E' P ⇒ M E P)

  asks : ∀ {A} → (E ⇒ A) ⊆ M E A
  asks = reader

module _ {M : Pt I ℓ}⦃ Mon : RawMPMonad M ⦄ where
  private module M = RawMPMonad Mon

  module _ {E}⦃ mono : Monotone E ⦄ where
    instance
      open RawMPMonad
      reader-monad : RawMPMonad (ReaderT E M)
      return reader-monad x e = M.return x
      _≥=_  reader-monad m f e = m e M.≥= λ i≤j px → f i≤j px (wk i≤j e)

      open ReaderMonad
      reader-monad-ops : ReaderMonad E (λ E → ReaderT E M)
      ask reader-monad-ops e = M.return e
      reader reader-monad-ops f e = M.return (f e)
      local reader-monad-ops f c e = c (f e)

  lift-reader : ∀ {P} E → M P ⊆ ReaderT E M P
  lift-reader _ z _ = z
