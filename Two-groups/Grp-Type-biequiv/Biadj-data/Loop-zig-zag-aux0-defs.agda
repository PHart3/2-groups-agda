{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.LoopSpace
open import 2Grp
open import 2GrpMap
open import 2Semigroup
open import 2SGrpMap
open import Hmtpy2Grp
open import KFunctor
open import LoopK-hom
open import LoopFunctor-ap
import Delooping

module Biadj-data.Loop-zig-zag-aux0-defs where

module Loop-zz-aux0-defs {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {x₀ : X} {y₀ : Y}
  (f : ⊙[ X , x₀ ] ⊙→ ⊙[ Y , y₀ ]) where

  open import SqKLoop
  open Delooping

  instance
  
    _ : has-level 1 (base (Ω ⊙[ X , x₀ ]) == base (Ω ⊙[ X , x₀ ]))
    _ = has-level-apply-instance {{K₂-is-2type (Ω ⊙[ X , x₀ ])}}

    _ : has-level 1 (base (Ω ⊙[ Y , y₀ ]) == base (Ω ⊙[ Y , y₀ ]))
    _ = has-level-apply-instance {{K₂-is-2type (Ω ⊙[ Y , y₀ ])}}

  α₁ =
    (assoc-wksgrphom 
      (grphom-forg (Loop2Grp-map f))
      (grphom-forg (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))))
      (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}}))

  α₂ =
    (assoc-wksgrphom
      (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
      (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))
      (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ X , x₀ ])))}}))

  α₃ =
    (assoc-wksgrphom
      (grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))))
      (idf2Mw {{sgrp (Loop2Grp (base (Ω ⊙[ Y , y₀ ])))}})
      (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)))))

  υ₁ =
    ! (natiso2G-to-== (Loop2Grp-map-∘ f (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})))) ∙
    ap Loop2Grp-map (⊙-crd∼-to-== (sq-KΩ x₀ y₀ f)) ∙
    natiso2G-to-== (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f)))

  υ₂0 = unit-wksgrphom-r (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))
  υ₂1 = unit-wksgrphom-l (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))

  𝕞 =
    natiso2G-to-==
      {μ =
        Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      {ν = Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
      (!ʷ (natiso-whisk-l {μ = grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})))} υ₂0))

  υ₂ =
    ! (natiso2G-to-==
        {μ = Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
        {ν = Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)) ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      υ₂0) ∙
    natiso2G-to-==
      {μ = Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
      {ν = cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}} ∘2G Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
      υ₂1

  τ₀ :
    Loop2Grp-map f ∘2G
    Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
    cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}
      =-=
    (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
    cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
    Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))
  τ₀ = 
    natiso2G-to-==
      {μ =
        Loop2Grp-map f ∘2G
        Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      {ν =
        (Loop2Grp-map f ∘2G
        Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      α₁ ◃∙
    ap (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}) υ₁ ◃∙
    ! (natiso2G-to-==
        {μ =
          Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        {ν =
          (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        α₂) ◃∙
    ap (λ m → Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G m) υ₂ ◃∙
    natiso2G-to-==
      {μ =
        Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}} ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
      {ν =
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
      α₃ ◃∎

  τ₁ = 
    natiso2G-to-==
      {μ =
        Loop2Grp-map f ∘2G
        Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      {ν =
        (Loop2Grp-map f ∘2G
        Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      α₁ ◃∙
    ap (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}) υ₁ ◃∙
    ! (natiso2G-to-==
        {μ =
          Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        {ν =
          (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        α₂) ◃∙
    ! (ap (λ m → Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G m)
        (natiso2G-to-== υ₂0)) ◃∙
    ap (λ m → Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G m)
      (natiso2G-to-== υ₂1) ◃∙
    natiso2G-to-==
      {μ =
        Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}} ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
      {ν =
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
      α₃ ◃∎

  τ₂ = 
    natiso2G-to-==
      {μ =
        Loop2Grp-map f ∘2G
        Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      {ν =
        (Loop2Grp-map f ∘2G
        Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      α₁ ◃∙
    ap (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}) υ₁ ◃∙
    ! (natiso2G-to-==
        {μ =
          Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        {ν =
          (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        α₂) ◃∙
    𝕞 ◃∙
    ap (λ m → Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G m)
      (natiso2G-to-== υ₂1) ◃∙
    natiso2G-to-==
      {μ =
        Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}} ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
      {ν =
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
      α₃ ◃∎

  τ₃ = 
    natiso2G-to-==
      {μ =
        Loop2Grp-map f ∘2G
        Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      {ν =
        (Loop2Grp-map f ∘2G
        Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      α₁ ◃∙
    ap (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}) υ₁ ◃∙
    ! (natiso2G-to-==
        {μ =
          Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        {ν =
          (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))) ∘2G
          cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
        α₂) ◃∙
    𝕞 ◃∙
    natiso2G-to-== (natiso-whisk-l {μ = grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})))} υ₂1) ◃∙
    natiso2G-to-==
      {μ =
        Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}} ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
      {ν =
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
      α₃ ◃∎

  τ₄ = 
    natiso2G-to-==
      {μ =
        Loop2Grp-map f ∘2G
        Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      {ν =
        (Loop2Grp-map f ∘2G
        Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      α₁ ◃∙
    ap (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}) υ₁ ◃∙
    natiso2G-to-==
      {μ =
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      {ν =
        Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      (!ʷ α₂) ◃∙
    𝕞 ◃∙
    natiso2G-to-== (natiso-whisk-l {μ = grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})))} υ₂1) ◃∙
    natiso2G-to-==
      {μ =
        Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}} ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
      {ν =
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
      α₃ ◃∎

  τ₅ = 
    natiso2G-to-==
      {μ =
        Loop2Grp-map f ∘2G
        Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      {ν =
        (Loop2Grp-map f ∘2G
        Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      α₁ ◃∙
    ! (ap (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}})
        (natiso2G-to-== (Loop2Grp-map-∘ f (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))))) ◃∙
    ap (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}})
      (ap Loop2Grp-map (⊙-crd∼-to-== (sq-KΩ x₀ y₀ f))) ◃∙
    ap (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}})
      (natiso2G-to-== (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f)))) ◃∙
    natiso2G-to-==
      {μ =
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      {ν =
        Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      (!ʷ α₂) ◃∙
    𝕞 ◃∙
    natiso2G-to-== (natiso-whisk-l {μ = grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})))} υ₂1) ◃∙
    natiso2G-to-==
      {μ =
        Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}} ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
      {ν =
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
      α₃ ◃∎

  τ₆ =  
    natiso2G-to-==
      {μ =
        Loop2Grp-map f ∘2G
        Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      {ν =
        (Loop2Grp-map f ∘2G
        Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      α₁ ◃∙
    natiso2G-to-== (!ʷ (natiso-whisk-r (Loop2Grp-map-∘ f (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))))) ◃∙
    ap (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}})
      (ap Loop2Grp-map (⊙-crd∼-to-== (sq-KΩ x₀ y₀ f))) ◃∙
    ap (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}})
      (natiso2G-to-== (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f)))) ◃∙
    natiso2G-to-==
      {μ =
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      {ν =
        Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      (!ʷ α₂) ◃∙
    𝕞 ◃∙
    natiso2G-to-== (natiso-whisk-l {μ = grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})))} υ₂1) ◃∙
    natiso2G-to-==
      {μ =
        Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}} ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
      {ν =
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
      α₃ ◃∎

  τ₇ = 
    natiso2G-to-==
      {μ =
        Loop2Grp-map f ∘2G
        Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      {ν =
        (Loop2Grp-map f ∘2G
        Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      α₁ ◃∙
    natiso2G-to-== (!ʷ (natiso-whisk-r (Loop2Grp-map-∘ f (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))))) ◃∙
    ap (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}})
      (ap Loop2Grp-map (⊙-crd∼-to-== (sq-KΩ x₀ y₀ f))) ◃∙
    natiso2G-to-== (natiso-whisk-r
      (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f)))) ◃∙
    natiso2G-to-==
      {μ =
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      {ν =
        Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      (!ʷ α₂) ◃∙
    𝕞 ◃∙
    natiso2G-to-== (natiso-whisk-l {μ = grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})))} υ₂1) ◃∙
    natiso2G-to-==
      {μ =
        Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}} ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
      {ν =
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
      α₃ ◃∎

  τ₈ = 
    natiso2G-to-==
      {μ =
        Loop2Grp-map f ∘2G
        Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      {ν =
        (Loop2Grp-map f ∘2G
        Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      α₁ ◃∙
    natiso2G-to-== (!ʷ (natiso-whisk-r (Loop2Grp-map-∘ f (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))))) ◃∙
    ap (λ m → m ∘2G cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}})
      (natiso2G-to-== (Loop2Grp-map-ap (sq-KΩ x₀ y₀ f))) ◃∙
    natiso2G-to-== (natiso-whisk-r
      (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f)))) ◃∙
    natiso2G-to-==
      {μ =
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      {ν =
        Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      (!ʷ α₂) ◃∙
    𝕞 ◃∙
    natiso2G-to-== (natiso-whisk-l {μ = grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})))} υ₂1) ◃∙
    natiso2G-to-==
      {μ =
        Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}} ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
      {ν =
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
      α₃ ◃∎

  τ₉ = 
    natiso2G-to-==
      {μ =
        Loop2Grp-map f ∘2G
        Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      {ν =
        (Loop2Grp-map f ∘2G
        Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      α₁ ◃∙
    natiso2G-to-== (!ʷ (natiso-whisk-r (Loop2Grp-map-∘ f (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))))) ◃∙
    natiso2G-to-==
      {μ =
        Loop2Grp-map (f ⊙∘ K₂-rec-hom {{Loop2Grp x₀}} x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      {ν =
        Loop2Grp-map (K₂-rec-hom {{Loop2Grp y₀}} y₀ (idf2G {{Loop2Grp y₀}}) ⊙∘ K₂-map⊙ (Loop2Grp-map-str f)) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      (natiso-whisk-r (Loop2Grp-map-ap (sq-KΩ x₀ y₀ f))) ◃∙
    natiso2G-to-== (natiso-whisk-r
      (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f)))) ◃∙
    natiso2G-to-==
      {μ =
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      {ν =
        Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}}
      (!ʷ α₂) ◃∙
    𝕞 ◃∙
    natiso2G-to-== (natiso-whisk-l {μ = grphom-forg (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})))} υ₂1) ◃∙
    natiso2G-to-==
      {μ =
        Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}} ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
      {ν =
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))}
      α₃ ◃∎
