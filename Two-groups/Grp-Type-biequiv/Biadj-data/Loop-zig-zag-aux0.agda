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
import Delooping
open import Biadj-data.Loop-zig-zag-defs

module Biadj-data.Loop-zig-zag-aux0 where

open CohGrp {{...}}
open CohGrpHom
open WkSGrpNatIso
open WkSGrpHomStr

module Loop-zz-aux0 {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {x₀ : X} {y₀ : Y}
  {f : ⊙[ X , x₀ ] ⊙→ ⊙[ Y , y₀ ]} where

  open import SqKLoop
  
  open Delooping
  open Loop-zz-defs f

  σ-trans =
    (assoc-wksgrphom
        (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
        (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ Y , y₀ ])))}})
        (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)))))
        natiso-∘
    (natiso-whisk-r (unit-wksgrphom-l (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))))
      natiso-∘
    (!ʷ (natiso-whisk-r (unit-wksgrphom-r (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)))))))
      natiso-∘
    (!ʷ (assoc-wksgrphom
      (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
      (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))
      (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}})))
      natiso-∘
    (natiso-whisk-r (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f))))
      natiso-∘
    (natiso-whisk-r (Loop2Grp-map-ap (sq-KΩ x₀ y₀ f)))
      natiso-∘
    (!ʷ (natiso-whisk-r (Loop2Grp-map-∘ f (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})))))
      natiso-∘
    (assoc-wksgrphom
      (grphom-forg (Loop2Grp-map f))
      (grphom-forg (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))))
      (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}}))

  abstract
    σ-translate : σ == natiso2G-to-== σ-trans
    σ-translate = =ₛ-out $
      natiso2G-to-==
        {μ =
          Loop2Grp-map f ∘2G
          Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        {ν =
          (Loop2Grp-map f ∘2G
          Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        (assoc-wksgrphom 
          (grphom-forg (Loop2Grp-map f))
          (grphom-forg (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}})) ◃∙
      ap (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}) (
        ! (natiso2G-to-== (Loop2Grp-map-∘ f (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})))) ∙
        ap Loop2Grp-map (⊙-crd∼-to-== (sq-KΩ x₀ y₀ f)) ∙
        natiso2G-to-== (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f)))) ◃∙
      ! (natiso2G-to-==
          {μ =
            Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
            Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)) ∘2G
            cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
          {ν =
            (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
            Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))) ∘2G
            cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
          (assoc-wksgrphom
            (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
            (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))
            (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}}))) ◃∙
      ap (λ m → Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G m)
        (! (natiso2G-to-== (unit-wksgrphom-r (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)))))) ∙
        natiso2G-to-== (unit-wksgrphom-l (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)))))) ◃∙
      natiso2G-to-==
        {μ =
          Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}} ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
        {ν =
          (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
        (assoc-wksgrphom
          (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ Y , y₀ ])))}})
          (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))) ◃∎
        =ₛ⟨ 3 & 1 & ap-!∙◃ (λ m → Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G m)
          (natiso2G-to-== (unit-wksgrphom-r (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))))
          (natiso2G-to-== (unit-wksgrphom-l (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)))))) ⟩
      natiso2G-to-==
        {μ =
          Loop2Grp-map f ∘2G
          Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        {ν =
          (Loop2Grp-map f ∘2G
          Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        (assoc-wksgrphom 
          (grphom-forg (Loop2Grp-map f))
          (grphom-forg (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}})) ◃∙
      ap (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}) (
        ! (natiso2G-to-== (Loop2Grp-map-∘ f (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})))) ∙
        ap Loop2Grp-map (⊙-crd∼-to-== (sq-KΩ x₀ y₀ f)) ∙
        natiso2G-to-== (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f)))) ◃∙
      ! (natiso2G-to-==
          {μ =
            Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
            Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)) ∘2G
            cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
          {ν =
            (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
            Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))) ∘2G
            cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
          (assoc-wksgrphom
            (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
            (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))
            (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}}))) ◃∙
      ! (ap (λ m → Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G m)
          (natiso2G-to-== (unit-wksgrphom-r (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))))) ◃∙
      ap (λ m → Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G m)
        (natiso2G-to-== (unit-wksgrphom-l (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)))))) ◃∙
      natiso2G-to-==
        {μ =
          Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}} ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
        {ν =
          (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
        (assoc-wksgrphom
          (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ Y , y₀ ])))}})
          (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))) ◃∎
        =ₛ₁⟨ 3 & 1 & !
          (!-whisk2G-conv-l (unit-wksgrphom-r (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)))))) ⟩
      natiso2G-to-==
        {μ =
          Loop2Grp-map f ∘2G
          Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        {ν =
          (Loop2Grp-map f ∘2G
          Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        (assoc-wksgrphom 
          (grphom-forg (Loop2Grp-map f))
          (grphom-forg (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}})) ◃∙
      ap (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}) (
        ! (natiso2G-to-== (Loop2Grp-map-∘ f (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})))) ∙
        ap Loop2Grp-map (⊙-crd∼-to-== (sq-KΩ x₀ y₀ f)) ∙
        natiso2G-to-== (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f)))) ◃∙
      ! (natiso2G-to-==
          {μ =
            Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
            Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)) ∘2G
            cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
          {ν =
            (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
            Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))) ∘2G
            cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
          (assoc-wksgrphom
            (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
            (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))
            (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}}))) ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-l
        (unit-wksgrphom-r (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))))) ◃∙
      ap (λ m → Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G m)
        (natiso2G-to-== (unit-wksgrphom-l (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)))))) ◃∙
      natiso2G-to-==
        {μ =
          Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}} ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
        {ν =
          (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
        (assoc-wksgrphom
          (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ Y , y₀ ])))}})
          (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))) ◃∎
        =ₛ₁⟨ 4 & 1 & ! (whisk2G-conv-l
          (unit-wksgrphom-l (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)))))) ⟩
      natiso2G-to-==
        {μ =
          Loop2Grp-map f ∘2G
          Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        {ν =
          (Loop2Grp-map f ∘2G
          Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        (assoc-wksgrphom 
          (grphom-forg (Loop2Grp-map f))
          (grphom-forg (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}})) ◃∙
      ap (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}) (
        ! (natiso2G-to-== (Loop2Grp-map-∘ f (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})))) ∙
        ap Loop2Grp-map (⊙-crd∼-to-== (sq-KΩ x₀ y₀ f)) ∙
        natiso2G-to-== (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f)))) ◃∙
      ! (natiso2G-to-==
          {μ =
            Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
            Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)) ∘2G
            cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
          {ν =
            (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
            Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))) ∘2G
            cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
          (assoc-wksgrphom
            (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
            (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))
            (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}}))) ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-l
        (unit-wksgrphom-r (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))))) ◃∙
      natiso2G-to-== (natiso-whisk-l (unit-wksgrphom-l (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)))))) ◃∙
      natiso2G-to-==
        {μ =
          Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}} ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
        {ν =
          (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
        (assoc-wksgrphom
          (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ Y , y₀ ])))}})
          (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))) ◃∎
        =ₛ₁⟨ 2 & 1 & ! (natiso2G-! $
          assoc-wksgrphom
            (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
            (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))
            (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}})) ⟩
      natiso2G-to-==
        {μ =
          Loop2Grp-map f ∘2G
          Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        {ν =
          (Loop2Grp-map f ∘2G
          Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        (assoc-wksgrphom 
          (grphom-forg (Loop2Grp-map f))
          (grphom-forg (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}})) ◃∙
      ap (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}) (
        ! (natiso2G-to-== (Loop2Grp-map-∘ f (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})))) ∙
        ap Loop2Grp-map (⊙-crd∼-to-== (sq-KΩ x₀ y₀ f)) ∙
        natiso2G-to-== (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f)))) ◃∙
      natiso2G-to-== (!ʷ
        (assoc-wksgrphom
          (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
          (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}}))) ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-l
        (unit-wksgrphom-r (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))))) ◃∙
      natiso2G-to-== (natiso-whisk-l (unit-wksgrphom-l (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)))))) ◃∙
      natiso2G-to-==
        {μ =
          Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}} ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
        {ν =
          (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
        (assoc-wksgrphom
          (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ Y , y₀ ])))}})
          (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))) ◃∎
        =ₛ⟨ 1 & 1 & ap-!∙∙◃ (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}})
          (natiso2G-to-== (Loop2Grp-map-∘ f (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))))
          (ap Loop2Grp-map (⊙-crd∼-to-== (sq-KΩ x₀ y₀ f)))
          (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f))) ⟩
      natiso2G-to-==
        {μ =
          Loop2Grp-map f ∘2G
          Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        {ν =
          (Loop2Grp-map f ∘2G
          Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        (assoc-wksgrphom 
          (grphom-forg (Loop2Grp-map f))
          (grphom-forg (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}})) ◃∙
      ! (ap (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}})
          (natiso2G-to-== (Loop2Grp-map-∘ f (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))))) ◃∙
      ap (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}})
        (ap Loop2Grp-map (⊙-crd∼-to-== (sq-KΩ x₀ y₀ f))) ◃∙
      ap (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}})
        (natiso2G-to-== (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f)))) ◃∙
      natiso2G-to-== (!ʷ
        (assoc-wksgrphom
          (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
          (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}}))) ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-l
        (unit-wksgrphom-r (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))))) ◃∙
      natiso2G-to-== (natiso-whisk-l (unit-wksgrphom-l (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)))))) ◃∙
      natiso2G-to-==
        {μ =
          Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}} ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
        {ν =
          (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
        (assoc-wksgrphom
          (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ Y , y₀ ])))}})
          (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))) ◃∎
        =ₛ₁⟨ 1 & 1 & ! (!-whisk2G-conv-r (Loop2Grp-map-∘ f (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})))) ⟩
      natiso2G-to-==
        {μ =
          Loop2Grp-map f ∘2G
          Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        {ν =
          (Loop2Grp-map f ∘2G
          Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        (assoc-wksgrphom 
          (grphom-forg (Loop2Grp-map f))
          (grphom-forg (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}})) ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-r (Loop2Grp-map-∘ f (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))))) ◃∙
      ap (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}})
        (ap Loop2Grp-map (⊙-crd∼-to-== (sq-KΩ x₀ y₀ f))) ◃∙
      ap (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}})
        (natiso2G-to-== (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f)))) ◃∙
      natiso2G-to-== (!ʷ
        (assoc-wksgrphom
          (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
          (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}}))) ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-r
        (unit-wksgrphom-r (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))))) ◃∙
      natiso2G-to-== (natiso-whisk-r (unit-wksgrphom-l (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)))))) ◃∙
      natiso2G-to-==
        {μ =
          Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}} ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
        {ν =
          (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
        (assoc-wksgrphom
          (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ Y , y₀ ])))}})
          (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))) ◃∎
        =ₛ₁⟨ 3 & 1 & ! (whisk2G-conv-r
          (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f)))) ⟩
      natiso2G-to-==
        {μ =
          Loop2Grp-map f ∘2G
          Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        {ν =
          (Loop2Grp-map f ∘2G
          Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        (assoc-wksgrphom 
          (grphom-forg (Loop2Grp-map f))
          (grphom-forg (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}})) ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-r (Loop2Grp-map-∘ f (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))))) ◃∙
      ap (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}})
        (ap Loop2Grp-map (⊙-crd∼-to-== (sq-KΩ x₀ y₀ f))) ◃∙
      natiso2G-to-== (natiso-whisk-r
        (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f)))) ◃∙
      natiso2G-to-== (!ʷ
        (assoc-wksgrphom
          (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
          (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}}))) ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-r
        (unit-wksgrphom-r (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))))) ◃∙
      natiso2G-to-== (natiso-whisk-r (unit-wksgrphom-l (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)))))) ◃∙
      natiso2G-to-==
        {μ =
          Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}} ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
        {ν =
          (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
        (assoc-wksgrphom
          (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ Y , y₀ ])))}})
          (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))) ◃∎
        =ₛ₁⟨ 2 & 1 & ap (ap (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}))
          (Ω-fmap-ap-pres (sq-KΩ x₀ y₀ f)) ⟩
      natiso2G-to-==
        {μ =
          Loop2Grp-map f ∘2G
          Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        {ν =
          (Loop2Grp-map f ∘2G
          Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        (assoc-wksgrphom 
          (grphom-forg (Loop2Grp-map f))
          (grphom-forg (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}})) ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-r (Loop2Grp-map-∘ f (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))))) ◃∙
      ap (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}})
        (natiso2G-to-== (Loop2Grp-map-ap (sq-KΩ x₀ y₀ f))) ◃∙
      natiso2G-to-== (natiso-whisk-r
        (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f)))) ◃∙
      natiso2G-to-== (!ʷ
        (assoc-wksgrphom
          (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
          (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}}))) ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-r
        (unit-wksgrphom-r (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))))) ◃∙
      natiso2G-to-== (natiso-whisk-r (unit-wksgrphom-l (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)))))) ◃∙
      natiso2G-to-==
        {μ =
          Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}} ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
        {ν =
          (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
        (assoc-wksgrphom
          (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ Y , y₀ ])))}})
          (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))) ◃∎
        =ₛ₁⟨ 2 & 1 & ! (whisk2G-conv-r (Loop2Grp-map-ap (sq-KΩ x₀ y₀ f))) ⟩
      natiso2G-to-==
        {μ =
          Loop2Grp-map f ∘2G
          Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        {ν =
          (Loop2Grp-map f ∘2G
          Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        (assoc-wksgrphom 
          (grphom-forg (Loop2Grp-map f))
          (grphom-forg (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}})) ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-r (Loop2Grp-map-∘ f (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))))) ◃∙
      natiso2G-to-== (natiso-whisk-r (Loop2Grp-map-ap (sq-KΩ x₀ y₀ f))) ◃∙
      natiso2G-to-== (natiso-whisk-r
        (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f)))) ◃∙
      natiso2G-to-== (!ʷ
        (assoc-wksgrphom
          (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
          (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}}))) ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-r
        (unit-wksgrphom-r (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))))) ◃∙
      natiso2G-to-== (natiso-whisk-r (unit-wksgrphom-l (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)))))) ◃∙
      natiso2G-to-==
        {μ =
          Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}} ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
        {ν =
          (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
        (assoc-wksgrphom
          (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ Y , y₀ ])))}})
          (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))) ◃∎
        =ₛ⟨ ∘2G-conv-oct
              (assoc-wksgrphom
                (grphom-forg (Loop2Grp-map f))
                (grphom-forg (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))))
                (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}}))
              (!ʷ (natiso-whisk-r (Loop2Grp-map-∘ f (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})))))
              (natiso-whisk-r (Loop2Grp-map-ap (sq-KΩ x₀ y₀ f)))
              (natiso-whisk-r (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f))))
              (!ʷ (assoc-wksgrphom
                (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
                (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))
                (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}})))
              (!ʷ (natiso-whisk-r (unit-wksgrphom-r (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)))))))
              (natiso-whisk-r (unit-wksgrphom-l (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))))
              (assoc-wksgrphom
                (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
                (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ Y , y₀ ])))}})
                (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))) ⟩
      natiso2G-to-== $
        (assoc-wksgrphom
          (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ Y , y₀ ])))}})
          (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)))))
          natiso-∘
        (natiso-whisk-r (unit-wksgrphom-l (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))))
          natiso-∘
        (!ʷ (natiso-whisk-r (unit-wksgrphom-r (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)))))))
          natiso-∘
        (!ʷ (assoc-wksgrphom
          (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
          (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}})))
          natiso-∘
        (natiso-whisk-r (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f))))
          natiso-∘
        (natiso-whisk-r (Loop2Grp-map-ap (sq-KΩ x₀ y₀ f)))
          natiso-∘
        (!ʷ (natiso-whisk-r (Loop2Grp-map-∘ f (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})))))
          natiso-∘
        (assoc-wksgrphom
          (grphom-forg (Loop2Grp-map f))
          (grphom-forg (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))))
          (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}})) ◃∎ ∎ₛ
