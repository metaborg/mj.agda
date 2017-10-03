open import MJ.Types
import MJ.Classtable.Core as Core

module MJ.Syntax.Program {c}(Ct : Core.Classtable c) where

open import Prelude hiding (erase)
open import Data.List.Most as List

open import MJ.Classtable.Code Ct
open import MJ.Syntax Ct

Prog : Ty c → Set
Prog a = Code × (Body [] a)
