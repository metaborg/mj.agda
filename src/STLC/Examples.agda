module STLC.Examples where

-- This file contains a few example programs for the definitional
-- interpreter for STLC in Section 2.

open import STLC.Semantics
open import Data.List.Most
open import Relation.Binary.PropositionalEquality -- for de Bruijn numerals
open import Data.Integer hiding (suc)
open import Agda.Builtin.Nat hiding (_+_)
open import Data.Maybe

-- The identity function: λ x . x
--
-- Variables are represented as de Bruijn indices, assumed to have
-- been elaborated from a surface language with names to the nameless
-- representation used in the abstract syntax in `STLC.Semantics`.
idexpr : Expr [] (unit ⇒ unit)
idexpr = ƛ (var (here refl))

-- id () = ()
test-idexpr : eval 2 (idexpr · unit) [] ≡ just unit
test-idexpr = refl


-- curried addition: λ x . λ y . y + x
curry+ : Expr [] (int ⇒ (int ⇒ int))
curry+ = ƛ (ƛ (iop _+_ (var (here refl)) (var (there (here refl)))))

-- 1 + 1 = 2
test-curry+ : eval 3 ((curry+ · (num (+ 1))) · (num (+ 1))) [] ≡ just (num (+ 2))
test-curry+ = refl
