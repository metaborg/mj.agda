{-
  This is the readme of the Agda mechanization accompanying our
  POPL 2018 paper:

    "Intrinsically-Typed Interpreters for Imperative Languages"

  The repository is hosted here:
  - https://github.com/metaborg/mj.agda

  A rendered and linked version of this readme can be found here:
  - https://metaborg.github.io/mj.agda/

  The current development uses do-notation syntactic sugar
  that is now part of Agda 2.5.4+ and will not compile with earlier versions.
  The POPL paper does *not* use do-notation; you may want to download the
  mj-1.0.0-popl18 release if you want a version compatible with the
  paper and Agda 2.5.3.

  If you have the right version of Agda installed, you should be able to run
  `make` in the project root. This will checkout the two dependencies in
  `./lib/` first and then build this `./Readme.agda` which serves as the main
  entrypoint to the development.

  Alternatively you can run `make docs` to build the html version of
  the development which is useful if you want to navigate the code
  (starting e.g. in `docs/index.html`) without having an editor setup
  for it. The html docs are syntax-highlighted and you can click
  references to navigate to their definitions.

  There are some differences between the Agda code used in the
  paper and this mechanization.  One general (but minor) discrepancy
  is that the definitions in the paper are typed in a manner that is
  not universe polymorphic.  However, the development makes extensive
  use of universe polymorphism, by explicitly quantifying over
  universe levels (e.g., `i` in `{i} → Set i`).

  Other discrepancies are summarized below in this readme.
-}

module Readme where

{-
  * Section 2 *

  We develop a monadic, well-typed interpreter for STLC and interpret
  a few example programs.

  Unlike the interpreter summarized in the paper, the STLC semantics
  in the development makes use of integers and integer operations.
-}
open import STLC.Semantics
open import STLC.Examples

{-
  * Section 3.1 - 3.3 *

  We demonstrate how naively extending the approach to cover
  imperative state is possible, but requires explicit weakening of
  bound values in the interpreter.
-}

open import STLCRef.SemanticsLB

{-
  * Section 3.4 : dependent passing style *

  We can improve the semantics with a form of monadic strength to get
  rid of explicit weakening.
-}
open import STLCRef.Semantics
open import STLCRef.Examples

{-
  * Section 4 until 4.3 *

  We implement the scopes and frames approach in the following small
  Agda library.
-}

open import ScopesFrames.ScopesFrames

{-
  * Section 4.4 *

  We demonstrate the basic usage of this library on an interpreter for
  STLC using scopes and frames.
-}
open import STLCSF.Semantics

{-
  * Section 5 *

  We show how our techniques scale by defining an intrinsically-typed
  interpreter for Middleweight Java (MJ), a language with:

  - Imperative objects
  - Sub-typing
  - Mutable, block-scoped environments
  - Early returns

  The only discrepancy between the code in this development and the
  code shown in the paper is the following:

  - Pattern matching lambdas are not useful for pattern matching
    against.  Instead of using `All` types with pattern matching
    lambdas (Section 5.3 and 5.4), we use tagging predicates in
    `MJSF.Syntax`.

  Then there are some notable differences between the original
  presentation of MJ and our development:

  - Original MJ distinguishes promotable expressions (method
    invocation and object creation) and all other expressions. We
    admit arbitrary expressions to be promoted. This does not change
    the semantics in any significant way. The expressions that we
    allow to be promoted are side-effect free.

  - returns are implemented by modeling non-void methods as having an
    expression as its last statement (technically, this is enforced by
    the type rules of Original MJ; in our development it is
    syntactically enforced).

  - MJ only has equality comparison expressions that can be used as
    conditional expressions.  We allow arbitrary expressions, and use
    if-zero (`ifz`) for conditionals.  This does not correspond to MJ
    or Java, but it would be straightforward to add Booleans and use a
    more conventional `if` statement instead.

  - If-zero statements have ordinary statements as their
    sub-statements.  These can either be block statements or any other
    statement which does not allocate a new frame.  In Original MJ, if
    statements must be blocks.

  - We include integers and integer operations, which are not in
    Original MJ.

  - Our MJ syntax admits fields typed by `void`, which Original MJ
    does not.

  - Our MJ syntax incorporates a dedicated `this` expression for
    referencing the "self" of an object.

-}

open import MJSF.Syntax
open import MJSF.Values
open import MJSF.Monad
open import MJSF.Semantics

{-
  We demonstrate that our interpreter is executable:
-}
open import MJSF.Examples.Integer
open import MJSF.Examples.DynamicDispatch


{-
  * Appendix A *

  The following code artifacts *are not* described in the paper, but
  are used as a comparison point to evaluate the impact on the
  interpreter of using the scopes and frames model of binding.

  This is an intrinsically-typed interpreter for MJ without the use of
  scope-and-frames. Instead it describes a language-*dependent*
  classtable construction to deal with object dot-access binding and
  typing contexts and environments to deal with lexical binding
  respectively.
-}
open import MJ.Syntax.Typed

-- lexical contexts
open import MJ.LexicalScope

-- class table
open import MJ.Classtable.Core
open import MJ.Classtable.Membership
open import MJ.Classtable.Code

-- semantics
open import MJ.Semantics.Values
open import MJ.Semantics.Environments
open import MJ.Semantics.Objects
open import MJ.Semantics.Objects.Flat
open import MJ.Semantics.Monadic

-- examples
open import MJ.Examples.Integer
open import MJ.Examples.Exceptions
open import MJ.Examples.While
open import MJ.Examples.DynDispatch

{-
  * Appendix B *

  Additionally we demonstrate briefly how Agda's typeclass mechanism
  is not sufficiently strong to infer store extension facts for
  weakening. (Notably Idris rejects an equivalent program as well
  because the two instances are overlapping)
-}
open import Experiments.Infer

{-
  * Appendix C *

  Our interpreters make use of the operator `_^_` operator, defined
  as:

  (1) `_^_ : ∀ {Σ Γ}{p q : List Type → Set} ⦃ w : Weakenable q ⦄ →
             M Γ p Σ → q Σ → M Γ (p ⊗ q) Σ`

  This operator is strikingly similar to the strength operator that is
  characteristic of strong monads:

  (2)  `_^_ : ∀ {p q} → M p → q → M (p ⊗ q)`

  Here, `p` and `q` are objects in a category ℂ, and M is a monad for
  ℂ.

  In the following development we show how to define a monad that is
  morally equivalent to ours.  The monad in the development below is
  defined over the category of monotone predicates.  In this category,
  the store-passing monad is a strong monad, with the usual notion of
  monadic strength, i.e., (2) above.

  We also show how, in this category, we can write an interpreter
  without explicit weakening, by writing the interpreter in a
  point-free style.
-}

-- open import Experiments.Category
-- open import Experiments.StrongMonad
-- open import Experiments.STLCRefPointfree

{-
  We briefly outline how these experiments relate to our paper.

  The interpreters in our paper are defined in terms of ordinary Agda
  functions and indexed types.  Agda functions and indexed types are
  not guaranteed to be weakenable, and Agda does not have built-in
  support for automatically weakening types across monadic binds.  In
  our paper, we address the weakening problem by making explicit use
  in our interpreters of the `_^_` operator, which is morally
  equivalent to the monadic strength operator for monotone predicates
  over store types, defined in the categorical development above.  Our
  `_^_` operator explicitly requires `q` to be weakenable, which is a
  fairly minimal requirement for convincing Agda's type checker that
  carrying types over monadic binds is safe.

  The categorical model enjoys a cleaner treatment of weakening, but
  it is more cumbersome to write interpreters in Agda using this
  model, because of the additional level of encoding imposed by
  constructing and working with objects and morphisms in a category,
  as encoded in Agda.  However, we imagine that the categorical
  development is a good target model for a future specification
  language for dynamic semantics.
-}
