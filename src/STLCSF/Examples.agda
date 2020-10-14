module STLCSF.Examples where

open import Data.Fin hiding (_+_)
open import Data.Product
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All
open import Data.Maybe
open import Data.Integer hiding (suc)

-- This file contains a few example programs for the definitional
-- interpreter for STLC using scopes and frames in Section 4.

open import Agda.Builtin.Nat hiding (_+_)
open import Relation.Binary.PropositionalEquality hiding ([_])

-- The identity function: λ x . x
module Id where

  open import STLCSF.Semantics 2
  open import ScopesFrames.ScopesFrames 2 Ty

  -- Whereas Agda can infer the structure of ordinary type contexts,
  -- the scope graph library represents scope graphs as "lookup
  -- tables".  Agda cannot straightforwardly infer the structure of a
  -- lookup table.  We spell it out.

  g : Graph
  g zero    = [] , [] -- root scope
  g (suc n) = [ unit ] , [ zero ] -- lexical scope for lambda

  -- Had we used the structural representation discussed in Section
  -- 4.2 ("A Note on Scope Representation"), Agda could infer the
  -- structure of scope graphs for STLC for us.  As summarized in that
  -- discussion, such a representation has other shortcomings, e.g.,
  -- when it comes to dealing with scope graphs that has actual graph
  -- structure (i.e. cyclic paths).
  --
  -- We assume that programs have been analyzed using the scope graph
  -- resolution calculus to construct scope graphs and replace named
  -- references with paths in programs.  In future work, we will
  -- explore how to automate this.  For now, we construct scope graphs
  -- manually.

  -- We load the syntax definition, specialized to our scope graph:
  open Syntax g
  open UsesGraph g

  idexpr : Expr zero (unit ⇒ unit)
  idexpr = ƛ {s' = suc zero} (var (path ([]) (here refl)))

  open UsesVal Val val-weaken
  
  -- Initial heap with an empty frame that is typed by the root scope:
  init-h : Heap [ zero ]
  init-h = ([] , []) ∷ []

  -- id () = ()
  test-idexpr : eval 2 (idexpr · unit) (here refl) init-h ≡ just (_ , _ , unit , _)
  test-idexpr = refl
  
  
module Curry where

  open import STLCSF.Semantics 3
  open import ScopesFrames.ScopesFrames 3 Ty

  -- Whereas Agda can infer the structure of ordinary type contexts,
  -- the scope graph library represents scope graphs as "lookup
  -- tables".  Agda cannot straightforwardly infer the structure of a
  -- lookup table.  We spell it out.

  g : Graph
  g zero          = [] , [] -- root scope
  g (suc (suc n)) = [ int ] , [ suc zero ] -- lexical scope for inner lambda
  g (suc n)       = [ int ] , [ zero ] -- lexical scope for outer

  -- Had we used the structural representation discussed in Section
  -- 4.2 ("A Note on Scope Representation"), Agda could infer the
  -- structure of scope graphs for STLC for us.  As summarized in that
  -- discussion, such a representation has other shortcomings, e.g.,
  -- when it comes to dealing with scope graphs that has actual graph
  -- structure (i.e. cyclic paths).
  --
  -- We assume that programs have been analyzed using the scope graph
  -- resolution calculus to construct scope graphs and replace named
  -- references with paths in programs.  In future work, we will
  -- explore how to automate this.  For now, we construct scope graphs
  -- manually.

  -- We load the syntax definition, specialized to our scope graph:
  open Syntax g
  open UsesGraph g

  -- curried addition: λ x . λ y . y + x
  curry+ : Expr zero (int ⇒ (int ⇒ int))
  curry+ = ƛ {s' = suc zero}
             (ƛ {s' = suc (suc zero)}
                (iop _+_
                     (var (path [] (here refl)))
                     (var (path ((here refl) ∷ []) (here refl)))))

  open UsesVal Val val-weaken
  
  -- Initial heap with an empty frame that is typed by the root scope:
  init-h : Heap [ zero ]
  init-h = ([] , []) ∷ []

  -- 1 + 1 = 2
  test-curry+ : eval 3 ((curry+ · (num (+ 1))) · (num (+ 1))) (here refl) init-h
                ≡ just (_ , _ , num (+ 2) , _)
  test-curry+ = refl
