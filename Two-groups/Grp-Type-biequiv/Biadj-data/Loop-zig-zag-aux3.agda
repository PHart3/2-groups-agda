{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=7 #-}

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
open import Biadj-data.Loop-zig-zag-aux2

module Biadj-data.Loop-zig-zag-aux3 where

module Loop-zz-aux3 {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {x₀ : X} {y₀ : Y}
  (f : ⊙[ X , x₀ ] ⊙→ ⊙[ Y , y₀ ]) where
  
  open Delooping
  open Loop-zz-defs f
  open Loop-zz-aux2 f

  abstract

    ρ₂-translate0 :
      ρ₂
        =ₛ
      ap (λ m → Loop2Grp-map f ∘2G m) (Loop-zz₀ x₀) ◃∙
      natiso2G-to-== ρ₂-trans-mid ◃∙
      ! (ap (λ m → m ∘2G Loop2Grp-map f) (Loop-zz₀ y₀)) ◃∎
    ρ₂-translate0 = =ₛ-in $
      ap (λ p →
           ap (λ m → Loop2Grp-map f ∘2G m) (Loop-zz₀ x₀) ∙
           p ∙
           ! (ap (λ m → m ∘2G Loop2Grp-map f) (Loop-zz₀ y₀)))
        ρ₂-mid-translate
      
    ρ₂-translate1 :
      ap (λ m → Loop2Grp-map f ∘2G m) (Loop-zz₀ x₀) ◃∙
      natiso2G-to-== ρ₂-trans-mid ◃∙
      ! (ap (λ m → m ∘2G Loop2Grp-map f) (Loop-zz₀ y₀)) ◃∎
        =ₛ
      ap (λ m → Loop2Grp-map f ∘2G m) (Loop-zz₀ x₀) ◃∙
      natiso2G-to-== ρ₂-trans-mid ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-r {μ = grphom-forg (Loop2Grp-map f)} (Loop-zz₀-iso y₀))) ◃∎
    ρ₂-translate1 = =ₛ-in $
      ap (λ p → ap (λ m → Loop2Grp-map f ∘2G m) (Loop-zz₀ x₀) ∙ natiso2G-to-== ρ₂-trans-mid ∙ p)
        (! (!-whisk2G-conv-r {f₁ = Loop2Grp-map f} (Loop-zz₀-iso {X = Y} y₀)))

    ρ₂-translate2 :
      ap (λ m → Loop2Grp-map f ∘2G m) (Loop-zz₀ x₀) ◃∙
      natiso2G-to-== ρ₂-trans-mid ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-r {μ = grphom-forg (Loop2Grp-map f)} (Loop-zz₀-iso y₀))) ◃∎
        =ₛ
      natiso2G-to-== (natiso-whisk-l {μ = grphom-forg (Loop2Grp-map f)} (Loop-zz₀-iso x₀)) ◃∙
      natiso2G-to-== ρ₂-trans-mid ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-r {μ = grphom-forg (Loop2Grp-map f)} (Loop-zz₀-iso y₀))) ◃∎
    ρ₂-translate2 = =ₛ-in $
      ap (λ p →
           p ∙
           natiso2G-to-== ρ₂-trans-mid ∙
           natiso2G-to-== (!ʷ (natiso-whisk-r {μ = grphom-forg (Loop2Grp-map f)} (Loop-zz₀-iso y₀))))
        (! (whisk2G-conv-l {f₂ = Loop2Grp-map f} (Loop-zz₀-iso x₀)))
        
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
