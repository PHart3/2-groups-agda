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
open import Biadj-data.Loop-zig-zag-aux0
open import Biadj-data.Loop-zig-zag-aux1-defs

module Biadj-data.Loop-zig-zag-aux1 where

module Loop-zz-aux1 {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}}
  {x₀ : X} {y₀ : Y} (f : ⊙[ X , x₀ ] ⊙→ ⊙[ Y , y₀ ]) where

  open import SqLoopK
  
  open Delooping
  open Loop-zz-defs f
  open Loop-zz-aux0 f
  open Loop-zz-aux1-defs f
  
  ρ₁-trans : CohGrpNatIso
    (Loop2Grp-map f ∘2G
    (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
    cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ X , x₀ ]))}}}}) ∘2G
    K₂-loopmap (Ω ⊙[ X , x₀ ]))
    (((Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
    cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}}) ∘2G
    K₂-loopmap (Ω ⊙[ Y , y₀ ])) ∘2G
    Loop2Grp-map f)
  ρ₁-trans =
    α₃
      natiso-∘
    (natiso-whisk-l
      {μ = grphom-forg $
        (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}})}
      (sq-ΩK (Loop2Grp-map-str f)))
      natiso-∘
    (!ʷ α₂)
      natiso-∘
    (natiso-whisk-r {μ = grphom-forg (K₂-loopmap (Ω ⊙[ X , x₀ ]))} σ-trans)
      natiso-∘
    α₁

  abstract
    ρ₁-translate-mid : τ₁ =ₛ τ₅
    ρ₁-translate-mid =
      τ₁
        =ₛ₁⟨ 2 & 1 & ! (whisk2G-conv-l (sq-ΩK (Loop2Grp-map-str f))) ⟩
      τ₂
        =ₛ₁⟨ 1 & 1 & ! (natiso2G-! α₂) ⟩
      τ₃
        =ₛ₁⟨ 0 & 1 & ap (ap (λ m → m ∘2G K₂-loopmap (Ω ⊙[ X , x₀ ]))) σ-translate ⟩
      τ₄
        =ₛ₁⟨ 0 & 1 & ! (whisk2G-conv-r σ-trans) ⟩
      τ₅ ∎ₛ

  abstract
    ρ₁-translate : ρ₁ =ₛ natiso2G-to-== ρ₁-trans ◃∎
    ρ₁-translate =
      ρ₁
        =ₛ⟨ 1 & 3 & ρ₁-translate-mid ⟩
      ρ₁-mid
        =ₛ⟨ ∘2G-conv-quint
              α₁
              (natiso-whisk-r {μ = grphom-forg (K₂-loopmap (Ω ⊙[ X , x₀ ]))} σ-trans)
              (!ʷ α₂)
              (natiso-whisk-l
                {μ = grphom-forg $
                  (Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
                  cohgrphom (idf _) {{idf2G {{Loop2Grp (base (Ω ⊙[ Y , y₀ ]))}}}})}
                (sq-ΩK (Loop2Grp-map-str f)))
              α₃ ⟩
      natiso2G-to-== ρ₁-trans ◃∎ ∎ₛ
