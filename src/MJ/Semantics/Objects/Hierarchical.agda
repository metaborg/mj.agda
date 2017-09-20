open import MJ.Types
open import MJ.Classtable
import MJ.Syntax as Syntax

module MJ.Semantics.Objects.Hierarchical {c}(Σ : CT c)(ℂ : Syntax.Impl Σ) where

open import Prelude

open import Level renaming (suc to lsuc; zero to lzero)
open import Data.List
open import Data.List.Any
open import Data.List.All as List∀
open import Data.List.All.Properties.Extra
open import Data.List.Prefix
open import Data.List.Properties.Extra
open import Data.Vec hiding (init)
open import Data.Vec.All as Vec∀ using ()
open import Data.Vec.All.Properties.Extra
open import Data.Maybe as Maybe hiding (All; map)
open import Data.Maybe.All as MayAll using ()
open import Relation.Binary.PropositionalEquality
open Membership-≡

open import MJ.Semantics.Values Σ
open import MJ.Syntax Σ
open CT Σ

record AllDecls {p}(P : ∀ ns → typing ns c → Set p)(c : Fin c) : Set p where
  inductive
  open Class (clookup c)
  field
    own : ∀ ns → All (P ns) (decls ns)
    inherited : Maybe.All (λ p → AllDecls P p) parent


private
  {-# NON_TERMINATING #-}
  decls-map : ∀ {C p q}{P : ∀ ns → typing ns c → Set p}{Q : ∀ ns → typing ns c → Set q} →
              (∀ {ns x} → P ns x → Q ns x) → AllDecls P C → AllDecls Q C
  decls-map f x = record {
        own = λ ns → List∀.map f (own ns)
      ; inherited = MayAll.map (λ p → decls-map f p) inherited
    }
    where open AllDecls x

  getter : ∀ {cid p ns a}{P : ∀ ns → typing ns c → Set p} → Member Σ cid ns a → AllDecls P cid → P ns a
  getter {ns = ns} (_ , refl , p) px = ∈-all p (AllDecls.own px ns)
  getter {cid = cid} (C , super u C<:P , def) record { own = own ; inherited = q } with
    clookup cid
  getter (C , super refl C<:P , def)
    record { own = own ; inherited = (just px) } | class .(just _) constr decls
    = getter (C , C<:P , def) px

  setter : ∀ {ns cid p a}{P : ∀ ns → typing ns c → Set p} → Member Σ cid ns a → P ns a →
            AllDecls P cid → AllDecls P cid
  setter {cid = cid} {P = P} (proj₃ , refl , pos) px record { own = own ; inherited = inherited } =
    record { own = own' ; inherited = inherited }
    where
      postulate own' : ∀ ns → All (P ns) (Class.decls (clookup cid) ns)
      {-}
      own' MTH = own MTH
      own' FLD = (own FLD) All[ pos ]≔' px
      -}

  setter {cid = cid} (C , super x sub , def) a₁ record { own = own ; inherited = _ }
    with clookup cid | inspect clookup cid
  setter (C , super refl sub , def) px
    record { own = own ; inherited = just pxs } | class .(just _) constr decls | [ eq ]
    = record {
      own =
        (λ ns → subst (λ C → All _ (Class.decls C ns)) (sym eq) (own ns)) ;
      inherited =
        subst (λ C → Maybe.All _ (Class.parent C)) (sym eq) (just (setter (C , sub , def) px pxs))
    }

encoding : ObjEncoding
encoding = record {
    Obj = λ W c → AllDecls (λ ns → MemVal {ns} W) c ;
    weaken-obj = λ cid ext O → decls-map (weaken-mv ext) O ;
    getter = λ O m → getter m O ;
    setter = λ O m v → setter m v O
  }
