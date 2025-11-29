{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=6 --lossy-unification #-}

open import lib.Basics
open import lib.types.LoopSpace
open import 2Grp
open import 2Semigroup
open import Hmtpy2Grp
open import KFunctor
open import LoopK-hom
import Delooping

-- the invertible modification making up the triangulator for our biadjoint biequivalence

open CohGrp {{...}}
open CohGrpHom
open WkSGrpNatIso
open WkSGrpHomStr

module Biadj-data.Loop-zig-zag where

module _ {i} {X : Type i} {{ηX : has-level 2 X}} (x₀ : X) where

  open Delooping (Ω ⊙[ X , x₀ ])

  Loop-zz₀ : CohGrpNatIso
    (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G cohgrphom _ {{idf2G {{Loop2Grp base}}}} ∘2G K₂-loopmap)
    (cohgrphom _ {{idf2G {{Loop2Grp x₀}}}})
  θ Loop-zz₀ p = K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) p
  θ-comp Loop-zz₀ x y = ! (=ₛ-out lemma)
    where abstract
      lemma :
        ! (ap2 _∙_
            (K₂-rec-hom-β-pts x₀ idf2G x)
            (K₂-rec-hom-β-pts x₀ idf2G y)) ◃∙
        map-comp
          (Loop2Grp-map (K₂-rec-hom x₀ idf2G) ∘2Gσ (cohgrphom _ {{idf2G {{Loop2Grp base}}}} ∘2G K₂-loopmap)) x y ◃∙
        K₂-rec-hom-β-pts x₀ idf2G (x ∙ y) ◃∎
          =ₛ
        idp ◃∎
      lemma = {!!}

module _ {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} (x₀ : X) (y₀ : Y)
  (f* : ⊙[ X , x₀ ] ⊙→ ⊙[ Y , y₀ ]) where

  open import SqKLoop
  
  open Delooping (Ω ⊙[ Y , y₀ ])

  Loop-zz₁ : (p : x₀ == x₀) → 
    K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (Ω-fmap f* p) ∙
    ! (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) p) ∙
    ! (Ω-fmap-∙ _ _) ∙
    Ω-fmap-ap (sq-KΩ x₀ y₀ f*) (map K₂-loopmap (Ω-fmap p)) ∙
    Ω-fmap-∙ _ _ ∙
    ap (Ω-fmap (⊙K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))) (K₂-map-β-pts (Ω-fmap f*) p) ∙
    idp
      ==
    idp
  Loop-zz₁ p = ?
