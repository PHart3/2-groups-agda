{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 #-}

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
open import Biadj-data.Loop-zig-zag-aux2a

module Biadj-data.Loop-zig-zag-aux2b where

module Loop-zz-aux2b {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {x₀ : X} {y₀ : Y}
  (f : ⊙[ X , x₀ ] ⊙→ ⊙[ Y , y₀ ]) where
  
  open Delooping
  open Loop-zz-defs f
  open Loop-zz-aux2a f

  instance
  
    _ : has-level 1 (base (Ω ⊙[ X , x₀ ]) == base (Ω ⊙[ X , x₀ ]))
    _ = has-level-apply-instance {{K₂-is-2type (Ω ⊙[ X , x₀ ])}}

    _ : has-level 1 (base (Ω ⊙[ Y , y₀ ]) == base (Ω ⊙[ Y , y₀ ]))
    _ = has-level-apply-instance {{K₂-is-2type (Ω ⊙[ Y , y₀ ])}}

  abstract

    ρ₂-translate0 :
      ρ₂
        =ₛ
      ap (λ m → Loop2Grp-map f ∘2G m) (Loop-zz₀ x₀) ◃∙
      natiso2G-to-== ρ₂-trans-mid ◃∙
      ! (ap (λ m → m ∘2G Loop2Grp-map f) (Loop-zz₀ y₀)) ◃∎
    ρ₂-translate0 =
      ρ₂
        =ₛ₁⟨ 1 & 1 & ρ₂-mid-translate ⟩
      ap (λ m → Loop2Grp-map f ∘2G m) (Loop-zz₀ x₀) ◃∙
      natiso2G-to-== ρ₂-trans-mid ◃∙
      ! (ap (λ m → m ∘2G Loop2Grp-map f) (Loop-zz₀ y₀)) ◃∎ ∎ₛ

    ρ₂-translate1 :
      ap (λ m → Loop2Grp-map f ∘2G m) (Loop-zz₀ x₀) ◃∙
      natiso2G-to-== ρ₂-trans-mid ◃∙
      ! (ap (λ m → m ∘2G Loop2Grp-map f) (Loop-zz₀ y₀)) ◃∎
        =ₛ
      ap (λ m → Loop2Grp-map f ∘2G m) (Loop-zz₀ x₀) ◃∙
      natiso2G-to-== ρ₂-trans-mid ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-r {μ = grphom-forg (Loop2Grp-map f)} (Loop-zz₀-iso y₀))) ◃∎
    ρ₂-translate1 =
      ap (λ m → Loop2Grp-map f ∘2G m) (Loop-zz₀ x₀) ◃∙
      natiso2G-to-== ρ₂-trans-mid ◃∙
      ! (ap (λ m → m ∘2G Loop2Grp-map f) (Loop-zz₀ y₀)) ◃∎
        =ₛ₁⟨ 2 & 1 & ! (!-whisk2G-conv-r {f₁ = Loop2Grp-map f} (Loop-zz₀-iso y₀)) ⟩
      ap (λ m → Loop2Grp-map f ∘2G m) (Loop-zz₀ x₀) ◃∙
      natiso2G-to-== ρ₂-trans-mid ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-r {μ = grphom-forg (Loop2Grp-map f)} (Loop-zz₀-iso y₀))) ◃∎ ∎ₛ

    ρ₂-translate2 :
      ap (λ m → Loop2Grp-map f ∘2G m) (Loop-zz₀ x₀) ◃∙
      natiso2G-to-== ρ₂-trans-mid ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-r {μ = grphom-forg (Loop2Grp-map f)} (Loop-zz₀-iso y₀))) ◃∎
        =ₛ
      natiso2G-to-== (natiso-whisk-l {μ = grphom-forg (Loop2Grp-map f)} (Loop-zz₀-iso x₀)) ◃∙
      natiso2G-to-== ρ₂-trans-mid ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-r {μ = grphom-forg (Loop2Grp-map f)} (Loop-zz₀-iso y₀))) ◃∎
    ρ₂-translate2 =
      ap (λ m → Loop2Grp-map f ∘2G m) (Loop-zz₀ x₀) ◃∙
      natiso2G-to-== ρ₂-trans-mid ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-r {μ = grphom-forg (Loop2Grp-map f)} (Loop-zz₀-iso y₀))) ◃∎
        =ₛ₁⟨ 0 & 1 & ! (whisk2G-conv-l {f₂ = Loop2Grp-map f} (Loop-zz₀-iso x₀)) ⟩
      natiso2G-to-== (natiso-whisk-l {μ = grphom-forg (Loop2Grp-map f)} (Loop-zz₀-iso x₀)) ◃∙
      natiso2G-to-== ρ₂-trans-mid ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-r {μ = grphom-forg (Loop2Grp-map f)} (Loop-zz₀-iso y₀))) ◃∎ ∎ₛ
