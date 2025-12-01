{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=7 --lossy-unification #-}

open import lib.Basics
open import lib.types.LoopSpace
open import 2Grp
open import 2GrpMap
open import 2Semigroup
open import Hmtpy2Grp
open import KFunctor
open import LoopK-hom
import Delooping
open import Biadj-data.Loop-zig-zag-ext

-- the invertible modification making up the triangulator for our biadjoint biequivalence

module Biadj-data.Loop-zig-zag where

open CohGrp {{...}}
open CohGrpHom
open WkSGrpNatIso
open WkSGrpHomStr

-- first component of triangulator
module _ {i} {X : Type i} {{ηX : has-level 2 X}} (x₀ : X) where

  open Delooping (Ω ⊙[ X , x₀ ])
  
  Loop-zz₀ :
    Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G cohgrphom _ {{idf2G {{Loop2Grp base}}}} ∘2G K₂-loopmap
      ==
    cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}
  Loop-zz₀ = natiso2G-to-== (Loop-zz₀-iso x₀)

-- second component of triangulator
module _ {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {x₀ : X} {y₀ : Y}
  (f : ⊙[ X , x₀ ] ⊙→ ⊙[ Y , y₀ ]) where

  open import SqKLoop
  open import SqLoopK
  
  open Delooping

  abstract
    Loop-zz₁ :
      ap (λ m →  m ∘2G Loop2Grp-map f) (Loop-zz₀ y₀) ◃∙
      ! (
      natiso2G-to-== (assoc-wksgrphom
        (grphom-forg (Loop2Grp-map f))
        (idf2Mw {{sgrp (Loop2Grp x₀)}})
        (idf2Mw {{sgrp (Loop2Grp x₀)}})) ∙
      ap (λ m → m ∘2G idf2Mw {{Loop2Grp x₀}})
        (! (natiso2G-to-== (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f)))) ∙
        natiso2G-to-== (unit-wksgrphom-l (grphom-forg (Loop2Grp-map f)))) ∙
      ! (natiso2G-to-== (assoc-wksgrphom
          (idf2Mw {{sgrp (Loop2Grp y₀)}})
          (grphom-forg (Loop2Grp-map f))
          (idf2Mw {{sgrp (Loop2Grp x₀)}}))) ∙
      ap (λ m → cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp x₀}}}} ∘2G m)
        (! (natiso2G-to-== (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f)))) ∙
        natiso2G-to-== (unit-wksgrphom-l (grphom-forg (Loop2Grp-map f)))) ∙
      natiso2G-to-== (assoc-wksgrphom
        (idf2Mw {{sgrp (Loop2Grp y₀)}})
        (idf2Mw {{sgrp (Loop2Grp y₀)}})
        (grphom-forg (Loop2Grp-map f)))) ◃∙
      ! (ap (λ m → Loop2Grp-map f ∘2G m) (Loop-zz₀ y₀)) ◃∙
      natiso2G-to-== (assoc-wksgrphom
        (grphom-forg (Loop2Grp-map f))
        (grphom-forg
          (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}))
        (grphom-forg (K₂-loopmap (Ω ⊙[ X , x₀ ])))) ◃∙
      ap (λ m → m ∘2G K₂-loopmap (Ω ⊙[ X , x₀ ])) (
        natiso2G-to-== (assoc-wksgrphom
          (grphom-forg (Loop2Grp-map f))
          (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})))
          (cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}})) ∙
        ap (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}) (
          ! (natiso2G-to-== (Loop2Grp-map-∘ f (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})))) ∙
          ap Loop2Grp-map (⊙-crd∼-to-== (sq-KΩ x₀ y₀ f)) ∙
          natiso2G-to-== (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f))))
        ! (natiso2G-to-== (assoc-wksgrphom
            (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})))
            (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))
            (cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}))) ∙
        ap (λ m → grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))) ∘2G m)
          (! (natiso2G-to-== (unit-wksgrphom-r (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)))))) ∙
          natiso2G-to-== (unit-wksgrphom-l (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)))))) ∙
        natiso2G-to-== (assoc-wksgrphom
          (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})))
          (cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}})
          (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)))))) ◃∙
      ! (natiso2G-to-== (assoc-wksgrphom
          (grphom-forg
            (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
            cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}))
          (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))
          (grphom-forg (K₂-loopmap (Ω ⊙[ X , x₀ ]))))) ◃∙
      ap (λ m →
           (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
           cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
           m)
         (natiso2G-to-== (sq-ΩK (str (Loop2Grp-map f)))) ◃∙
      natiso2G-to-== (assoc-wksgrphom
        (grphom-forg
          (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}))
        (grphom-forg (K₂-loopmap (Ω ⊙[ Y , y₀ ])))
        (grphom-forg (Loop2Grp-map f))) ◃∎
        =ₛ
      idp ◃∎
    Loop-zz₁ = =ₛ-out $
