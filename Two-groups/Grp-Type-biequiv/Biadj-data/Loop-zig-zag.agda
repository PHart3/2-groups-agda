{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=6 --lossy-unification #-}

open import lib.Basics
open import lib.types.LoopSpace
open import 2Grp
open import 2Semigroup
open import Hmtpy2Grp
open import KFunctor
open import SqLoopK
open import SqKLoop
open import LoopK-hom

-- first zig-zag modification for our biequivalence data

module Biadj-data.Loop-zig-zag where

module _ {i} {X : Type i} {{ηX : has-level 2 X}} (x₀ : X) where

  open import Delooping (Ω ⊙[ X , x₀ ])

  open CohGrp {{...}}
  open WkSGrpNatIso
  open WkSGrpHomStr

  Loop-zz : CohGrpNatIso
    (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G cohgrphom _ {{idf2G {{Loop2Grp base}}}} ∘2G K₂-loopmap)
    (cohgrphom _ {{idf2G {{Loop2Grp x₀}}}})
  θ Loop-zz p = K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) p
  θ-comp Loop-zz x y = ! (=ₛ-out lemma)
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
