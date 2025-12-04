{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import lib.types.LoopSpace
open import 2Grp
open import 2GrpMap
open import 2Semigroup
open import 2SGrpMap
open import Hmtpy2Grp
open import KFunctor
open import LoopK-hom
import Delooping
open import Biadj-data.Loop-zig-zag-defs
open import Biadj-data.Loop-zig-zag-aux0

module Biadj-data.Loop-zig-zag-aux1-defs where

module Loop-zz-aux1-defs {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}}
  {x₀ : X} {y₀ : Y} (f : ⊙[ X , x₀ ] ⊙→ ⊙[ Y , y₀ ]) where

  open import SqLoopK
  
  open Delooping
  open Loop-zz-defs f
  open Loop-zz-aux0 f

  instance
  
    _ : has-level 1 (base (Ω ⊙[ X , x₀ ]) == base (Ω ⊙[ X , x₀ ]))
    _ = has-level-apply-instance {{K₂-is-2type (Ω ⊙[ X , x₀ ])}}

    _ : has-level 1 (base (Ω ⊙[ Y , y₀ ]) == base (Ω ⊙[ Y , y₀ ]))
    _ = has-level-apply-instance {{K₂-is-2type (Ω ⊙[ Y , y₀ ])}}

  α₁ =
    assoc-wksgrphom 
      (grphom-forg (Loop2Grp-map f))
      (grphom-forg
        (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}))
      (grphom-forg (K₂-loopmap (Ω ⊙[ X , x₀ ])))

  α₂ =
    assoc-wksgrphom
      (grphom-forg
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}))
      (grphom-forg (Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))))
      (grphom-forg (K₂-loopmap (Ω ⊙[ X , x₀ ])))

  α₃ =
    assoc-wksgrphom
      (grphom-forg
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}))
      (grphom-forg (K₂-loopmap (Ω ⊙[ Y , y₀ ])))
      (grphom-forg (Loop2Grp-map f))

  ρ₁-mid = 
    natiso2G-to-==
      {μ =
        Loop2Grp-map f ∘2G
        (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}) ∘2G
        K₂-loopmap (Ω ⊙[ X , x₀ ])}
      {ν =
        (Loop2Grp-map f ∘2G
        (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}})) ∘2G
        K₂-loopmap (Ω ⊙[ X , x₀ ])}
      α₁ ◃∙
    natiso2G-to-== (natiso-whisk-r {μ = grphom-forg (K₂-loopmap (Ω ⊙[ X , x₀ ]))} σ-trans) ◃∙
    natiso2G-to-==
      {μ =
        ((Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
         cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))) ∘2G
        K₂-loopmap (Ω ⊙[ X , x₀ ])}
      {ν =
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
         cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)) ∘2G
        K₂-loopmap (Ω ⊙[ X , x₀ ])}
      (!ʷ α₂) ◃∙
    natiso2G-to-== (natiso-whisk-l
      {μ = grphom-forg $
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}})}
      (sq-ΩK (Loop2Grp-map-str f))) ◃∙
    natiso2G-to-==
      {μ =
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
         cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
        K₂-loopmap (Ω ⊙[ Y , y₀ ]) ∘2G
        Loop2Grp-map f}
      {ν =
        ((Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
         cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
        K₂-loopmap (Ω ⊙[ Y , y₀ ])) ∘2G
        Loop2Grp-map f}
      α₃ ◃∎

  τ₁ =
    ap (λ m → m ∘2G K₂-loopmap (Ω ⊙[ X , x₀ ])) σ ◃∙
    ! (natiso2G-to-==
        {μ =
          (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
           cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)) ∘2G
          K₂-loopmap (Ω ⊙[ X , x₀ ])}
        {ν =
          ((Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
           cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))) ∘2G
          K₂-loopmap (Ω ⊙[ X , x₀ ])}
        α₂) ◃∙
    ap (λ m →
         (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
         cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
         m)
       (natiso2G-to-== (sq-ΩK (Loop2Grp-map-str f))) ◃∎

  τ₂ :
    (Loop2Grp-map f ∘2G
    (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
    cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}})) ∘2G
    K₂-loopmap (Ω ⊙[ X , x₀ ])
      =-=
    (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
    cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
    K₂-loopmap (Ω ⊙[ Y , y₀ ]) ∘2G
    Loop2Grp-map f
  τ₂ =
    ap (λ m → m ∘2G K₂-loopmap (Ω ⊙[ X , x₀ ])) σ ◃∙
    ! (natiso2G-to-==
        {μ =
          (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
           cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)) ∘2G
          K₂-loopmap (Ω ⊙[ X , x₀ ])}
        {ν =
          ((Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
           cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
          Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))) ∘2G
          K₂-loopmap (Ω ⊙[ X , x₀ ])}
        α₂) ◃∙
    natiso2G-to-== (natiso-whisk-l
      {μ = grphom-forg $
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}})}
      (sq-ΩK (Loop2Grp-map-str f))) ◃∎

  τ₃ :
    (Loop2Grp-map f ∘2G
    (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
    cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}})) ∘2G
    K₂-loopmap (Ω ⊙[ X , x₀ ])
      =-=
    (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
    cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
    K₂-loopmap (Ω ⊙[ Y , y₀ ]) ∘2G
    Loop2Grp-map f
  τ₃ =
    ap (λ m → m ∘2G K₂-loopmap (Ω ⊙[ X , x₀ ])) σ ◃∙
    natiso2G-to-==
      {μ =
        ((Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
         cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))) ∘2G
        K₂-loopmap (Ω ⊙[ X , x₀ ])}
      {ν =
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
         cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)) ∘2G
        K₂-loopmap (Ω ⊙[ X , x₀ ])}
      (!ʷ α₂) ◃∙
    natiso2G-to-== (natiso-whisk-l
      {μ = grphom-forg $
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}})}
      (sq-ΩK (Loop2Grp-map-str f))) ◃∎

  τ₄ :
    (Loop2Grp-map f ∘2G
    (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
    cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}})) ∘2G
    K₂-loopmap (Ω ⊙[ X , x₀ ])
      =-=
    (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
    cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
    K₂-loopmap (Ω ⊙[ Y , y₀ ]) ∘2G
    Loop2Grp-map f
  τ₄ =
    ap (λ m → m ∘2G K₂-loopmap (Ω ⊙[ X , x₀ ])) (natiso2G-to-== σ-trans) ◃∙
    natiso2G-to-==
      {μ =
        ((Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
         cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))) ∘2G
        K₂-loopmap (Ω ⊙[ X , x₀ ])}
      {ν =
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
         cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)) ∘2G
        K₂-loopmap (Ω ⊙[ X , x₀ ])}
      (!ʷ α₂) ◃∙
    natiso2G-to-== (natiso-whisk-l
      {μ = grphom-forg $
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}})}
      (sq-ΩK (Loop2Grp-map-str f))) ◃∎

  τ₅ :
    (Loop2Grp-map f ∘2G
    (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
    cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}})) ∘2G
    K₂-loopmap (Ω ⊙[ X , x₀ ])
      =-=
    (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
    cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
    K₂-loopmap (Ω ⊙[ Y , y₀ ]) ∘2G
    Loop2Grp-map f
  τ₅ = 
    natiso2G-to-== (natiso-whisk-r {μ = grphom-forg (K₂-loopmap (Ω ⊙[ X , x₀ ]))} σ-trans) ◃∙
    natiso2G-to-==
      {μ =
        ((Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
         cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
        Loop2Grp-map (K₂-action-hom (Loop2Grp-map f))) ∘2G
        K₂-loopmap (Ω ⊙[ X , x₀ ])}
      {ν =
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
         cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
       Loop2Grp-map (K₂-action-hom (Loop2Grp-map f)) ∘2G
        K₂-loopmap (Ω ⊙[ X , x₀ ])}
      (!ʷ α₂) ◃∙
    natiso2G-to-== (natiso-whisk-l
      {μ = grphom-forg $
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}})}
      (sq-ΩK (Loop2Grp-map-str f))) ◃∎
