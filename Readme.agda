{-
  Difference from main artifact:
  - Vectors for graphs, instead of functions-as-lookup-tables.
  - Explicitly parameterized types instead of using modules.
  - Using Agda stdlib v0.16
-}

module Readme where

open import STLC.Semantics
open import STLC.Examples

open import STLCRef.SemanticsLB

open import STLCRef.Semantics
open import STLCRef.Examples

open import ScopesFrames.ScopeGraph
open import ScopesFrames.FrameHeap


open import STLCSF.Semantics

open import MJSF.Syntax
open import MJSF.Values
open import MJSF.Monad
open import MJSF.Semantics

open import MJSF.Examples.Integer
open import MJSF.Examples.DynamicDispatch


