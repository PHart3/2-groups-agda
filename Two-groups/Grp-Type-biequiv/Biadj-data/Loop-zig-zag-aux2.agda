{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=7 --lossy-unification #-}

open import lib.Basics
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
open import Biadj-data.Loop-zig-zag-aux2-defs

module Biadj-data.Loop-zig-zag-aux2 where

module Loop-zz-aux2 {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {x₀ : X} {y₀ : Y}
  (f : ⊙[ X , x₀ ] ⊙→ ⊙[ Y , y₀ ]) where
  
  open Delooping
  open Loop-zz-aux2-defs f

  ρ₂-trans-mid : CohGrpNatIso
    (Loop2Grp-map f ∘2G
    cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}} ∘2G
    cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}})
    ((cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
    cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}}) ∘2G
    Loop2Grp-map f)
  ρ₂-trans-mid = 
    α₃
      natiso-∘
    (natiso-whisk-l (unit-wksgrphom-l (grphom-forg (Loop2Grp-map f))))
      natiso-∘
    (!ʷ (natiso-whisk-l (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f)))))
      natiso-∘
    (!ʷ α₂)
      natiso-∘
    (natiso-whisk-r (unit-wksgrphom-l (grphom-forg (Loop2Grp-map f))))
      natiso-∘
    (!ʷ (natiso-whisk-r (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f)))))
      natiso-∘
    α₁

  abstract
  
    ρ₂-mid-translate0 : τ₁ =ₛ τ₅
    ρ₂-mid-translate0 = 
      τ₁
        =ₛ⟨ 3 & 1 & ap-!∙◃ (λ m → cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G m)
          (natiso2G-to-== (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f))))
          (natiso2G-to-== (unit-wksgrphom-l (grphom-forg (Loop2Grp-map f)))) ⟩
      τ₂
        =ₛ₁⟨ 4 & 1 & ! (whisk2G-conv-l (unit-wksgrphom-l (grphom-forg (Loop2Grp-map f)))) ⟩
      τ₃
        =ₛ₁⟨ 3 & 1 & ! (!-whisk2G-conv-l (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f)))) ⟩        
      τ₄
        =ₛ₁⟨ 2 & 1 & ! (natiso2G-! α₂) ⟩
      τ₅ ∎ₛ

    ρ₂-mid-translate1 : τ₅ =ₛ natiso2G-to-== ρ₂-trans-mid ◃∎
    ρ₂-mid-translate1 = 
      τ₅
        =ₛ⟨ 1 & 1 & ap-!∙◃ (λ m → m ∘2G cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}})
          (natiso2G-to-== (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f))))
          (natiso2G-to-== {μ = Loop2Grp-map f} (unit-wksgrphom-l (grphom-forg (Loop2Grp-map f)))) ⟩
      τ₆
        =ₛ₁⟨ 2 & 1 & ! (whisk2G-conv-r (unit-wksgrphom-l (grphom-forg (Loop2Grp-map f)))) ⟩
      τ₇
        =ₛ₁⟨ 1 & 1 & ! (!-whisk2G-conv-r (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f)))) ⟩
      τ₈
        =ₛ⟨ ∘2G-conv-sept        
              α₁
              (!ʷ (natiso-whisk-r (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f)))))
              (natiso-whisk-r (unit-wksgrphom-l (grphom-forg (Loop2Grp-map f))))
              (!ʷ α₂)
              (!ʷ (natiso-whisk-l (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f)))))
              (natiso-whisk-l (unit-wksgrphom-l (grphom-forg (Loop2Grp-map f))))
              α₃ ⟩
      natiso2G-to-== ρ₂-trans-mid ◃∎ ∎ₛ

  ρ₂-mid-translate-ₛ : τ₁ =ₛ natiso2G-to-== ρ₂-trans-mid ◃∎
  ρ₂-mid-translate-ₛ = ρ₂-mid-translate0 ∙ₛ ρ₂-mid-translate1

  abstract
    ρ₂-mid-translate : ↯ τ₁ == natiso2G-to-== ρ₂-trans-mid
    ρ₂-mid-translate = =ₛ-out ρ₂-mid-translate-ₛ

  ρ₂-trans : CohGrpNatIso
    (Loop2Grp-map f ∘2G
    (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
    cohgrphom _ {{idf2G {{Loop2Grp (base _)}}}}) ∘2G
    K₂-loopmap (Ω ⊙[ X , x₀ ]))
    (((Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
    cohgrphom _ {{idf2G {{Loop2Grp (base _)}}}}) ∘2G
    K₂-loopmap (Ω ⊙[ Y , y₀ ])) ∘2G
    Loop2Grp-map f)
  ρ₂-trans =
    !ʷ (natiso-whisk-r {μ = grphom-forg (Loop2Grp-map f)} (Loop-zz₀-iso y₀))
      natiso-∘
    ρ₂-trans-mid
      natiso-∘
    natiso-whisk-l {μ = grphom-forg (Loop2Grp-map f)} (Loop-zz₀-iso x₀)
