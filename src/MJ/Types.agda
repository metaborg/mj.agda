module MJ.Types where

open import Prelude hiding (_≟_)
open import Data.Fin.Properties as FinP using ()
open import Data.Vec
open import Data.List

open import Relation.Binary.Core
open import Relation.Nullary

data Cid (c : ℕ) : Set where
  cls : Fin c → Cid c
  Object : Cid c

_cid≟_ : ∀ {c} → Decidable (_≡_ {A = Cid c})
cls x cid≟ cls y with x FinP.≟ y
cls x cid≟ cls .x | yes refl = yes refl
cls x cid≟ cls y | no ¬p = no (λ{ refl → ¬p refl})
cls x cid≟ Object = no (λ ())
Object cid≟ cls x = no (λ ())
Object cid≟ Object = yes refl

data Ty (c : ℕ) : Set where
  void : Ty c
  int  : Ty c
  bool : Ty c
  ref  : Cid c → Ty c

data Ty⁺ (c : ℕ) : Set where
  vty : Ty c → Ty⁺ c
  obj : Cid c → Ty⁺ c

World : ℕ → Set
World c = List (Ty⁺ c)

Sig : ℕ → Set
Sig c = List (Ty c) × Ty c

_≟_ : ∀ {c} → Decidable (_≡_ {A = Ty c})
void ≟ void = yes refl
void ≟ int = no (λ ())
void ≟ ref x = no (λ ())
void ≟ bool = no (λ ())
int ≟ void = no (λ ())
int ≟ int = yes refl
int ≟ ref x = no (λ ())
int ≟ bool = no (λ ())
ref x ≟ void = no (λ ())
ref x ≟ int = no (λ ())
ref x ≟ bool = no (λ ())
ref x ≟ ref y with x cid≟ y
ref x ≟ ref y | yes p = yes (cong ref p)
ref x ≟ ref y | no ¬p = no λ{ refl → ¬p refl }
bool ≟ bool = yes refl
bool ≟ void = no (λ ())
bool ≟ int = no (λ ())
bool ≟ ref x = no (λ ())
