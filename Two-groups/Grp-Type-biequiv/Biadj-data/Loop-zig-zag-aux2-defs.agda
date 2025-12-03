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

module Biadj-data.Loop-zig-zag-aux0-defs where

module Loop-zz-aux2-defs {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {x₀ : X} {y₀ : Y}
  (f : ⊙[ X , x₀ ] ⊙→ ⊙[ Y , y₀ ]) where

  open Delooping
  open Loop-zz-defs f

  instance
  
    _ : has-level 1 (base (Ω ⊙[ X , x₀ ]) == base (Ω ⊙[ X , x₀ ]))
    _ = has-level-apply-instance {{K₂-is-2type (Ω ⊙[ X , x₀ ])}}

    _ : has-level 1 (base (Ω ⊙[ Y , y₀ ]) == base (Ω ⊙[ Y , y₀ ]))
    _ = has-level-apply-instance {{K₂-is-2type (Ω ⊙[ Y , y₀ ])}}

  α₁ =
    (assoc-wksgrphom
      (grphom-forg (Loop2Grp-map f))
      (idf2Mw {{sgrp (Loop2Grp x₀)}})
      (idf2Mw {{sgrp (Loop2Grp x₀)}}))

  α₂ =
    (assoc-wksgrphom
      (idf2Mw {{sgrp (Loop2Grp y₀)}})
      (grphom-forg (Loop2Grp-map f))
      (idf2Mw {{sgrp (Loop2Grp x₀)}}))

  α₃ =
    (assoc-wksgrphom
      (idf2Mw {{sgrp (Loop2Grp y₀)}})
      (idf2Mw {{sgrp (Loop2Grp y₀)}})
      (grphom-forg (Loop2Grp-map f)))    

  τ₁ :
    Loop2Grp-map f ∘2G
    cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}} ∘2G
    cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}
      =-=
    (cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
    cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}}) ∘2G
    Loop2Grp-map f
  τ₁ = 
    natiso2G-to-==
      {ν =
         (Loop2Grp-map f ∘2G
         cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}) ∘2G
         cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}}
      α₁ ◃∙
    ap (λ m → m ∘2G cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}})
      (! (natiso2G-to-== (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f)))) ∙
      natiso2G-to-== {μ = Loop2Grp-map f} (unit-wksgrphom-l (grphom-forg (Loop2Grp-map f)))) ◃∙
    ! (natiso2G-to-==
        {μ =
          cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
          (Loop2Grp-map f ∘2G
          cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}})}
        {ν =
          (cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
          Loop2Grp-map f) ∘2G
          cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}}
        α₂) ◃∙
    ap (λ m → cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G m)
      (! (natiso2G-to-== (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f)))) ∙
      natiso2G-to-== (unit-wksgrphom-l (grphom-forg (Loop2Grp-map f)))) ◃∙
    natiso2G-to-==
      {μ =
        cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        (cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        Loop2Grp-map f)}
      {ν =
        (cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}}) ∘2G
        Loop2Grp-map f}
      α₃ ◃∎

  τ₂ =
    natiso2G-to-==
      {ν =
         (Loop2Grp-map f ∘2G
         cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}) ∘2G
         cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}}
      α₁ ◃∙
    ap (λ m → m ∘2G cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}})
      (! (natiso2G-to-== (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f)))) ∙
      natiso2G-to-== {μ = Loop2Grp-map f} (unit-wksgrphom-l (grphom-forg (Loop2Grp-map f)))) ◃∙
    ! (natiso2G-to-==
        {μ =
          cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
          (Loop2Grp-map f ∘2G
          cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}})}
        {ν =
          (cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
          Loop2Grp-map f) ∘2G
          cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}}
        α₂) ◃∙
    ! (ap (λ m → cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G m)
        (natiso2G-to-== (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f))))) ◃∙
    ap (λ m → cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G m)
      (natiso2G-to-== (unit-wksgrphom-l (grphom-forg (Loop2Grp-map f)))) ◃∙
    natiso2G-to-==
      {μ =
        cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        (cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        Loop2Grp-map f)}
      {ν =
        (cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}}) ∘2G
        Loop2Grp-map f}
      α₃ ◃∎

  τ₃ =
    natiso2G-to-==
      {ν =
         (Loop2Grp-map f ∘2G
         cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}) ∘2G
         cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}}
      α₁ ◃∙
    ap (λ m → m ∘2G cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}})
      (! (natiso2G-to-== (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f)))) ∙
      natiso2G-to-== {μ = Loop2Grp-map f} (unit-wksgrphom-l (grphom-forg (Loop2Grp-map f)))) ◃∙
    ! (natiso2G-to-==
        {μ =
          cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
          (Loop2Grp-map f ∘2G
          cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}})}
        {ν =
          (cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
          Loop2Grp-map f) ∘2G
          cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}}
        α₂) ◃∙
    ! (ap (λ m → cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G m)
        (natiso2G-to-== (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f))))) ◃∙
    natiso-whisk-l (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f))) ◃∙
    natiso2G-to-==
      {μ =
        cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        (cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        Loop2Grp-map f)}
      {ν =
        (cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}}) ∘2G
        Loop2Grp-map f}
      α₃ ◃∎

  τ₄
    natiso2G-to-==
      {ν =
         (Loop2Grp-map f ∘2G
         cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}) ∘2G
         cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}}
      α₁ ◃∙
    ap (λ m → m ∘2G cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}})
      (! (natiso2G-to-== (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f)))) ∙
      natiso2G-to-== {μ = Loop2Grp-map f} (unit-wksgrphom-l (grphom-forg (Loop2Grp-map f)))) ◃∙
    ! (natiso2G-to-==
        {μ =
          cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
          (Loop2Grp-map f ∘2G
          cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}})}
        {ν =
          (cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
          Loop2Grp-map f) ∘2G
          cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}}
        α₂) ◃∙
    natiso2G-to-== (!ʷ (natiso-whisk-l (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f))))) ◃∙
    natiso2G-to-== (natiso-whisk-l (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f)))) ◃∙
    natiso2G-to-==
      {μ =
        cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        (cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        Loop2Grp-map f)}
      {ν =
        (cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}}) ∘2G
        Loop2Grp-map f}
      α₃ ◃∎

  τ₅ = 
    natiso2G-to-==
      {ν =
         (Loop2Grp-map f ∘2G
         cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}) ∘2G
         cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}}
      α₁ ◃∙
    ap (λ m → m ∘2G cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}})
      (! (natiso2G-to-== (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f)))) ∙
      natiso2G-to-== {μ = Loop2Grp-map f} (unit-wksgrphom-l (grphom-forg (Loop2Grp-map f)))) ◃∙
    natiso2G-to-==
      {μ =
        (cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        Loop2Grp-map f) ∘2G
        cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}}
      {ν =
        cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        (Loop2Grp-map f ∘2G
        cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}})}
      (!ʷ α₂) ◃∙
    natiso2G-to-== (!ʷ (natiso-whisk-l (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f))))) ◃∙
    natiso2G-to-== (natiso-whisk-l (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f)))) ◃∙
    natiso2G-to-==
      {μ =
        cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        (cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        Loop2Grp-map f)}
      {ν =
        (cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}}) ∘2G
        Loop2Grp-map f}
      α₃ ◃∎

  τ₆ =
    natiso2G-to-==
      {ν =
         (Loop2Grp-map f ∘2G
         cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}) ∘2G
         cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}}
      α₁ ◃∙
    ! (ap (λ m → m ∘2G cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}})
        (natiso2G-to-== (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f))))) ◃∙
    ap (λ m → m ∘2G cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}})
      (natiso2G-to-== {μ = Loop2Grp-map f} (unit-wksgrphom-l (grphom-forg (Loop2Grp-map f)))) ◃∙
    natiso2G-to-==
      {μ =
        (cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        Loop2Grp-map f) ∘2G
        cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}}
      {ν =
        cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        (Loop2Grp-map f ∘2G
        cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}})}
      (!ʷ α₂) ◃∙
    natiso2G-to-== (!ʷ (natiso-whisk-l (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f))))) ◃∙
    natiso2G-to-== (natiso-whisk-l (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f)))) ◃∙
    natiso2G-to-==
      {μ =
        cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        (cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        Loop2Grp-map f)}
      {ν =
        (cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}}) ∘2G
        Loop2Grp-map f}
      α₃ ◃∎

  τ₇ = 
    natiso2G-to-==
      {ν =
         (Loop2Grp-map f ∘2G
         cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}) ∘2G
         cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}}
      α₁ ◃∙
    ! (ap (λ m → m ∘2G cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}})
        (natiso2G-to-== (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f))))) ◃∙        
    natiso2G-to-== (natiso-whisk-r (unit-wksgrphom-l (grphom-forg (Loop2Grp-map f)))) ◃∙
    natiso2G-to-==
      {μ =
        (cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        Loop2Grp-map f) ∘2G
        cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}}
      {ν =
        cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        (Loop2Grp-map f ∘2G
        cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}})}
      (!ʷ α₂) ◃∙
    natiso2G-to-== (!ʷ (natiso-whisk-l (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f))))) ◃∙
    natiso2G-to-== (natiso-whisk-l (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f)))) ◃∙
    natiso2G-to-==
      {μ =
        cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        (cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        Loop2Grp-map f)}
      {ν =
        (cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}}) ∘2G
        Loop2Grp-map f}
      α₃ ◃∎

  τ₈ = 
    natiso2G-to-==
      {ν =
        (Loop2Grp-map f ∘2G
        cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}) ∘2G
        cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}}
      α₁ ◃∙
    natiso2G-to-== (!ʷ (natiso-whisk-r (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f))))) ◃∙        
    natiso2G-to-== (natiso-whisk-r (unit-wksgrphom-l (grphom-forg (Loop2Grp-map f)))) ◃∙
    natiso2G-to-==
      {μ =
        (cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        Loop2Grp-map f) ∘2G
        cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}}
      {ν =
        cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        (Loop2Grp-map f ∘2G
        cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}})}
      (!ʷ α₂) ◃∙
    natiso2G-to-== (!ʷ (natiso-whisk-l (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f))))) ◃∙
    natiso2G-to-== (natiso-whisk-l (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f)))) ◃∙
    natiso2G-to-==
      {μ =
        cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        (cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        Loop2Grp-map f)}
      {ν =
        (cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}}) ∘2G
        Loop2Grp-map f}
      α₃ ◃∎
