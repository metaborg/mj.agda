module Prelude where

open import Data.Nat public
open import Data.Nat.Properties.Simple public
open import Data.Fin using (Fin; #_; suc; zero) public

open import Data.Unit using (tt; ⊤) public
open import Data.Empty public
open import Data.Bool using (true; false; Bool) public

open import Data.Product public using (∃; ∃₂; _×_; _,_; proj₁; proj₂; ,_) public

open import Relation.Binary.PropositionalEquality hiding ([_]) public
open ≡-Reasoning public

open import Relation.Nullary public
open import Relation.Nullary.Decidable using (True) public

open import Function using (_∘_; _$_; id; const; flip) public
