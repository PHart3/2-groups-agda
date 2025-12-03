{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=7 --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.LoopSpace
open import 2Grp
open import 2GrpMap
open import 2GrpMap-conv
open import 2Semigroup
open import 2SGrpMap
open import Hmtpy2Grp
open import KFunctor
open import LoopK-hom
open import LoopFunctor-ap
open import SqKLoop
import Delooping
open import Biadj-data.Loop-zig-zag-aux0-defs

module Biadj-data.Loop-zig-zag-aux0 where

module Loop-zz-aux0 {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {x₀ : X} {y₀ : Y}
  (f : ⊙[ X , x₀ ] ⊙→ ⊙[ Y , y₀ ]) where

  open Delooping
  open Loop-zz-aux0-defs f

  σ-trans :
    CohGrpNatIso
      (Loop2Grp-map f ∘2G
      Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
      cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}})
      ((Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
      cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
      Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)))
  σ-trans =
    α₃
      natiso-∘
    (natiso-whisk-l υ₂1)
      natiso-∘
    (!ʷ (natiso-whisk-l υ₂0))
      natiso-∘
    (!ʷ α₂)
      natiso-∘
    (natiso-whisk-r (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f))))
      natiso-∘
    (natiso-whisk-r (Loop2Grp-map-ap (sq-KΩ x₀ y₀ f)))
      natiso-∘
    (!ʷ (natiso-whisk-r (Loop2Grp-map-∘ f (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})))))
      natiso-∘
    α₁

  abstract
  
    σ-translate0 : τ₀ =ₛ τ₄
    σ-translate0 =
      τ₀
        =ₛ⟨ 3 & 1 & ap-!∙◃ (λ m → Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G m)
            (natiso2G-to-== υ₂0)
            (natiso2G-to-== υ₂1) ⟩
      τ₁
        =ₛ₁⟨ 3 & 1 & ! (!-whisk2G-conv-l υ₂0) ⟩
      τ₂
        =ₛ₁⟨ 4 & 1 & ! (whisk2G-conv-l υ₂1) ⟩
      τ₃
        =ₛ₁⟨ 2 & 1 & ! (natiso2G-! $
          assoc-wksgrphom
            (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
            (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))
            (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}})) ⟩
      τ₄ ∎ₛ
      
    σ-translate1 : τ₄ =ₛ τ₇
    σ-translate1 = 
      τ₄
        =ₛ⟨ 1 & 1 & ap-!∙∙◃ (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}})
          (natiso2G-to-== (Loop2Grp-map-∘ f (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))))
          (ap Loop2Grp-map (⊙-crd∼-to-== (sq-KΩ x₀ y₀ f)))
          (natiso2G-to-== (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f)))) ⟩
      τ₅
        =ₛ₁⟨ 1 & 1 & ! (!-whisk2G-conv-r (Loop2Grp-map-∘ f (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})))) ⟩
      τ₆
        =ₛ₁⟨ 3 & 1 & ! (whisk2G-conv-r
          (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f)))) ⟩
      τ₇ ∎ₛ

    σ-translate2 : τ₇ =ₛ natiso2G-to-== σ-trans ◃∎
    σ-translate2 = 
      τ₇
        =ₛ₁⟨ 2 & 1 & ap (ap (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}))
          (Ω-fmap-ap-pres (sq-KΩ x₀ y₀ f)) ⟩
      τ₈
        =ₛ₁⟨ 2 & 1 & ! (whisk2G-conv-r (Loop2Grp-map-ap (sq-KΩ x₀ y₀ f))) ⟩
      τ₉
        =ₛ⟨ ∘2G-conv-oct
              α₁
              (!ʷ (natiso-whisk-r (Loop2Grp-map-∘ f (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})))))
              (natiso-whisk-r (Loop2Grp-map-ap (sq-KΩ x₀ y₀ f)))
              (natiso-whisk-r (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f))))
              (!ʷ α₂)
              (!ʷ (natiso-whisk-l υ₂0))
              (natiso-whisk-l υ₂1)
              α₃ ⟩
      natiso2G-to-== σ-trans ◃∎ ∎ₛ

  abstract
    σ-translate : τ₀ =ₛ natiso2G-to-== σ-trans ◃∎
    σ-translate = σ-translate0 ∙ₛ σ-translate1 ∙ₛ σ-translate2
