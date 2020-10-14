module STLCRef.Examples where

-- This file contains a few example programs for the definitional
-- interpreter for STLC+Ref using monadic strength, defined in Section
-- 3.

open import STLCRef.Semantics
open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All
open import Relation.Binary.PropositionalEquality
open import Data.Integer hiding (suc)
open import Agda.Builtin.Nat hiding (_+_)
open import Data.Maybe
open import Data.Product

-------------------
-- STLC FRAGMENT --
-------------------

-- The identity function: λ x . x
idexpr : Expr [] (unit ⇒ unit)
idexpr = ƛ (var (here refl))

-- id () = ()
test-idexpr : eval 2 (idexpr · unit) [] [] ≡ just (_ , [] , unit , _)
test-idexpr = refl


-- curried addition: λ x . λ y . y + x
curry+ : Expr [] (int ⇒ (int ⇒ int))
curry+ = ƛ (ƛ (iop _+_ (var (here refl)) (var (there (here refl)))))

-- 1 + 1 = 2
test-curry+ : eval 3 ((curry+ · (num (+ (suc zero)))) · (num (+ (suc zero)))) [] []
              ≡ just (_ , [] , num (+ (suc (suc zero))) , _)
test-curry+ = refl


------------------
-- REF FRAGMENT --
------------------

-- Sugar for let: LET e1 e2 = (λ x . e2) e1
LET : ∀ {Γ a b} → Expr Γ a → Expr (a ∷ Γ) b → Expr Γ b
LET bnd bod = (ƛ bod) · bnd

-- Factorial function, defined via Landin's knot:
--
-- let r = ref (λ x . x) in
-- let f = λ n . ifz n then 1 else n * (!r (n - 1)) in
-- let _ = r := f in
-- f 4
landin-fac : Expr [] int
landin-fac =
  LET (ref {t = int ⇒ int} (ƛ (var (here refl))))
  (LET (ƛ {a = int} (ifz (var (here refl))
                         (num (+ 1))
                         (iop (Data.Integer._*_) (var (here refl))
                              ((! (var (there (here refl)))) · (iop (Data.Integer._-_) (var (here refl)) (num (+ 1)))))))
  (LET ((var (there (here refl))) ≔ var (here refl))
  (var (there (here refl))) · (num (+ 4))))

test-landin-fac : eval 20 landin-fac [] [] ≡ just (_ , _ , num (+ 24) , _)
test-landin-fac = refl

-- Divergence via Landin's knot:
--
-- let r = ref (λ x . x) in
-- let f = λ x . !r 0 in
-- let _ = r := f in
-- f 0
landin-div : Expr [] int
landin-div =
  LET (ref {t = int ⇒ int} (ƛ (var (here refl))))
  (LET (ƛ {a = int} ((! (var (there (here refl)))) · num (+ zero)))
  (LET ((var (there (here refl))) ≔ var (here refl))
  (var (there (here refl))) · (num (+ zero))))


test-landin-div : eval 1337 landin-div [] [] ≡ nothing
test-landin-div = refl

