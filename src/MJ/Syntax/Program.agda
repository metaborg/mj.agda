open import MJ.Types
import MJ.Classtable.Core as Core

module MJ.Syntax.Program {c}(Ct : Core.Classtable c) where

open import Prelude hiding (erase)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Maybe.All as MayAll
open import Data.Vec as Vec hiding (_∈_)
open import Data.Star as Star
open import Data.List.Most as List
open import Data.List.Properties.Extra as List+
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Data.String

import Data.Vec.All as Vec∀

open Core c
open Classtable Ct
open import MJ.Classtable.Membership Ct
open import MJ.Classtable.Code Ct
open import MJ.LexicalScope Ct
open import MJ.Syntax Ct

Prog : Ty c → Set
Prog a = Code × (Body [] a)
