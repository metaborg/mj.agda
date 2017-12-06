module Categorical.Monad.Identity where

open import Categories.Category
open import Categories.Functor.Core renaming (id to idF)
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.Monad
open import Categories.Support.Equivalence
open import Categories.Support.SetoidFunctions as SF hiding (id)

open Category
open Monad

idM : ∀ {o l e} → (C : Category o l e) → Monad C
F (idM C) = idF
η (idM C) = idN
μ (idM C) = idN
assoc (idM C) =
  begin
    C [ id C ∘ id C ]
  ↓⟨ identityˡ C ⟩
    id C
  ↑⟨ identityˡ C ⟩
    C [ id C ∘ id C ]
  ∎
  where open HomReasoning C
identityˡ (idM C) = identityˡ C
identityʳ (idM C) = identityʳ C
