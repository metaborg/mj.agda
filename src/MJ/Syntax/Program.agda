open import MJ.Types
import MJ.Classtable.Core as Core

module MJ.Syntax.Program {c}(Ct : Core.Classtable c) where

open import Prelude
open import Data.List

open import MJ.Classtable.Code Ct
open import MJ.Syntax Ct

Prog : Ty c → Set
Prog a = Code × (Body [] a)
