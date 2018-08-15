open import MJ.Types

open import Data.Nat
open import Data.Maybe hiding (monad)
open import Data.Sum
open import Data.Product
open import Data.List.Most
open import Data.Empty

import MJ.Classtable.Core as Core
import MJ.Classtable.Code as Code

import MJ.Syntax as Syntax
import MJ.Semantics.Values as Values

module MJ.Semantics {c}(Ct : Core.Classtable c)(ℂ : Code.Code Ct) where

open import MJ.Syntax.Program Ct
open import MJ.Semantics.Objects.Flat Ct using (encoding)
open import MJ.Semantics.Objects Ct
open ObjEncoding encoding renaming (StoreVal to StoreVal')
open Values Ct

-- functional big-step definitional interpreter
-- open import MJ.Semantics.Functional Σ ℂ
open import MJ.Semantics.Monadic Ct ℂ public
open import MJ.Semantics.Monad Ct Exception  public

open Monadic
  M
  monad
  m-has-reader
  m-has-heap
  m-has-timeout
  m-has-error

eval : ∀ {a} → ℕ → Prog a → Maybe (∃ λ W → Store W × (Exception ⊎ Val W a))
eval k (lib , main) with eval-body k main [] []
eval k (lib , main) | just (_ , _ , μ , v) = just (, μ , v)
... | nothing = nothing

{-
a few predicates on program interpretation:
... saying it will terminate succesfully in a state where P holds
-}
_⇓⟨_⟩_ : ∀ {a} → Prog a → ℕ → (P : ∀ {W} → Val W a → Set) → Set
p ⇓⟨ k ⟩ P with eval k p
p ⇓⟨ k ⟩ P | just (_ , _ , inj₂ v) = P v
p ⇓⟨ k ⟩ P | just (_ , _ , inj₁ e) = ⊥
p ⇓⟨ k ⟩ P | nothing = ⊥

{-
...saying it will raise an exception in a state where P holds
-}
_⇓⟨_⟩!_ : ∀ {a} → Prog a → ℕ → (P : ∀ {W} → Store W → Exception → Set) → Set
p ⇓⟨ k ⟩! P with eval k p
p ⇓⟨ k ⟩! P | nothing = ⊥
p ⇓⟨ k ⟩! P | just (_ , _ , inj₂ _) = ⊥
p ⇓⟨ k ⟩! P | just (_ , μ , inj₁ e) = P μ e
