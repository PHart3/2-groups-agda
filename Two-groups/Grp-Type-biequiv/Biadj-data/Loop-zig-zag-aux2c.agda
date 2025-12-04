{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=7 --lossy-unification #-}

open import lib.Basics
open import lib.types.LoopSpace
open import 2Grp
open import 2GrpMap
open import 2GrpMap-conv
open import 2Semigroup
open import 2SGrpMap
open import NatIso
open import Hmtpy2Grp
open import KFunctor
open import LoopK-hom
import Delooping
open import Biadj-data.Loop-zig-zag-defs
open import Biadj-data.Loop-zig-zag-aux2a
open import Biadj-data.Loop-zig-zag-aux2b

module Biadj-data.Loop-zig-zag-aux2c where

module Loop-zz-aux2c {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {x₀ : X} {y₀ : Y}
  (f : ⊙[ X , x₀ ] ⊙→ ⊙[ Y , y₀ ]) where
  
  open Delooping
  open Loop-zz-defs f
  open Loop-zz-aux2a f
  open Loop-zz-aux2b f

  abstract
    ρ₂-translate3 :
      natiso2G-to-== (natiso-whisk-l {μ = grphom-forg (Loop2Grp-map f)} (Loop-zz₀-iso x₀)) ◃∙
      natiso2G-to-== ρ₂-trans-mid ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-r {μ = grphom-forg (Loop2Grp-map f)} (Loop-zz₀-iso y₀))) ◃∎
        =ₛ
      natiso2G-to-== ρ₂-trans ◃∎
    ρ₂-translate3 = !ₛ (∘2G-conv-tri
      (natiso-whisk-l {μ = grphom-forg (Loop2Grp-map f)} (Loop-zz₀-iso x₀))
      ρ₂-trans-mid
      (!ʷ (natiso-whisk-r {μ = grphom-forg (Loop2Grp-map f)} (Loop-zz₀-iso y₀))))

  abstract
    ρ₂-translate : ρ₂ =ₛ natiso2G-to-== ρ₂-trans ◃∎
    ρ₂-translate = ρ₂-translate0 ∙ₛ ρ₂-translate1 ∙ₛ ρ₂-translate2 ∙ₛ ρ₂-translate3

  ρ₂-trans' : CohGrpNatIso
    (Loop2Grp-map f ∘2G
    (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
    cohgrphom _ {{idf2G {{Loop2Grp (base _)}}}}) ∘2G
    K₂-loopmap (Ω ⊙[ X , x₀ ]))
    (((Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
    cohgrphom _ {{idf2G {{Loop2Grp (base _)}}}}) ∘2G
    K₂-loopmap (Ω ⊙[ Y , y₀ ])) ∘2G
    Loop2Grp-map f)
  ρ₂-trans' =
    !ʷ (natiso-whisk-r {μ = grphom-forg (Loop2Grp-map f)} (Loop-zz₀-iso y₀))
      natiso-∘
    (ρ₂-trans-mid
      natiso-∘'
    natiso-whisk-l {μ = grphom-forg (Loop2Grp-map f)} (Loop-zz₀-iso x₀))

  abstract
    ρ₂-translate'-aux : ρ₂-trans == ρ₂-trans'
    ρ₂-translate'-aux =
      ap (λ n →
             !ʷ (natiso-whisk-r {μ = grphom-forg (Loop2Grp-map f)} (Loop-zz₀-iso y₀)) natiso-∘ n)
        (natiso-∘=∘' {n₁ = ρ₂-trans-mid}
          (natiso-whisk-l {μ = grphom-forg (Loop2Grp-map f)} (Loop-zz₀-iso x₀)))

  abstract
    ρ₂-translate' : ρ₂ =ₛ natiso2G-to-== ρ₂-trans' ◃∎
    ρ₂-translate' = ρ₂-translate ∙ₛ =ₛ-in (ap natiso2G-to-== ρ₂-translate'-aux)
        
