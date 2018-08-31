open import Relation.Binary.Core
open import Agda.Primitive

module Relation.Unary.Weakening {a b}
                                (X : Set a)
                                (_≤_ : X → X → Set b)
                                (≤-refl  : Reflexive _≤_)
                                (≤-trans : Transitive _≤_)
                                {c}
                                (P : X → Set c) where

record Wk : Set (a ⊔ b ⊔ c) where
  field
    wk : {x y : X} → x ≤ y → P x → P y

-- Proof-based version
record Wk-pf : Set (a ⊔ b ⊔ c) where
  field
    wk       : {x y : X} → x ≤ y → P x → P y
    wk-refl  : {x : X} {p : P x} → wk {x = x} ≤-refl p ≡ p
    wk-trans : {x y z : X} {p : P x} {x≤y : x ≤ y} {y≤z : y ≤ z} →
               wk y≤z (wk x≤y p) ≡ wk (≤-trans x≤y y≤z) p

Wk-pf-to-Wk : Wk-pf → Wk
Wk-pf-to-Wk wk-pf =
  record { wk = Wk-pf.wk wk-pf }


