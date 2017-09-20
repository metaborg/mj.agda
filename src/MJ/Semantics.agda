open import MJ.Types
import MJ.Classtable.Core as Core
import MJ.Classtable.Code as Code

import MJ.Syntax as Syntax
import MJ.Semantics.Values as Values

module MJ.Semantics {c}(Ct : Core.Classtable c)(ℂ : Code.Code Ct) where

-- functional big-step definitional interpreter
-- open import MJ.Semantics.Functional Σ ℂ
open import MJ.Semantics.Monadic Ct ℂ public
