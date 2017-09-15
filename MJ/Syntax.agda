open import MJ.Types
open import MJ.Classtable

module MJ.Syntax {c}(Σ : Classtable c) where

open import MJ.Syntax.Typed Σ public
