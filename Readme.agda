module Readme where

{-

This repository contains the Agda mechanization that belongs with our
POPL 2018 paper: Intrinsically Typed Interpreters for Imperative Languages.

This development has been tested against Agda 2.5.3.
If you have this installed you should be able simply run `make` in the
project root, which will checkout some libraries in `./lib/` first and
then build `./src/Readme.agda` which serves as the main entrypoint
to the development.

Alternatively you can run `make doc` to build the html version of the development
which is useful if you want to navigate the code (starting e.g. in `doc/Readme.html`)
without having an editor setup for it.
The html docs are syntax-highlighted and you can click references to navigate
to their definitions.

-}

{-
  We develop a monadic, well-typed interpreter
  for STLC and interpret a few example programs.
-}
open import STLC.Semantics
open import STLC.Examples

{-
  And demonstrate how naively extending the approach to cover
  imperative state is possible, but requires explicit weakening
  of bound values in the interpreter:
-}
open import STLCRef.SemanticsLB

{-
  We can improve the semantics with a form of monadic strength
  and get rid of explicit weakening.
-}
open import STLCRef.Semantics
open import STLCRef.Examples

{-
  We take these techniques and show that they scale
  by giving an intrinsically typed interpreter for
  Middleweight Java.
  A language with:

  - Imperative objects
  - Sub-typing
  - Mutable, block-scoped environments
  - Exceptions and early returns
-}
open import MJ.Syntax.Typed
open import MJ.Semantics.Values
open import MJ.Semantics.Objects.Flat
open import MJ.Semantics.Monadic
open import MJ.Examples.Integer
open import MJ.Examples.Exceptions

{-
  Like many imperative languages the MJ development uses a variety
  of binding patterns.
  We show how we can use the Scopes & Frames approach to model
  these patterns uniformly in a well-typed manner

  To that end we first develop a language independent mechanization of
  the Scopes & Frames model of binding:
-}
open import ScopeGraph.ScopesFrames

{-
  And demonstrate its basic usage by writing an
  interpreter for STLC where scopes are used to capture lexical binding
  and frames are used to model lexical environments.
-}
open import STLCSF.Semantics

{-
  Again we scale it to the size of Middleweight Java:
-}
open import MJSF.Syntax
open import MJSF.Values
open import MJSF.Monad
open import MJSF.Semantics

{-
  And demonstrate that it is executable:
-}
open import MJSF.Examples.Integer

{-
  Additionally we demonstrate briefly how Agda's typeclass mechanism
  is not sufficiently strong to infer store extension facts for weakening.
  (Notably rejects equivalent as well because the two instances are overlapping)
-}
open import Experiments.Infer

{-
There are a few discrepancies with paper:

- Universe polymorphic definitions in the development are presented in
  their simplified (monomorphic) form in the paper

- MJSF: pattern matching lambdas are not useful for pattern matching
  against, which we need in order to initialize method and field slots.
  Instead of having the `All` with the pattern matching lambda, we use a
  tagging predicate; e.g. `#m`.  This is morally equivalent to the `All`
  used in the paper (Section 5.4).

Then there are a few notable differences between the original presentation
of MJ and our development:

- MJ distinguishes promotable expressions (method invocation and object
  creation) and all other expressions.  We admit arbitrary expressions
  to be promoted.  This does not change the semantics in any significant
  way.  The expressions that we allow to be promoted are side-effect
  free.

- returns are implemented by modeling non-void methods as having an
  expression as its last statement (like in MJ).

- MJ only has equality comparison expressions that can be used as
  conditional expressions.  We allow arbitrary expressions, and use
  `ifz`.  It would be straightforward to add booleans.

- If statements have ordinary statements as their sub-statements.  These
  can either be block statements or any other statement which does not
  allocate a new frame.
-}
