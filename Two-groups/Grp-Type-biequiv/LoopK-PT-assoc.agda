{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=5 --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.LoopSpace
open import 2Grp
open import 2Semigroup
open import 2SGrpMap
open import 2GrpMap
open import Hmtpy2Grp
open import Delooping
open import KFunctor
open import KFunctor-comp
open import SqLoopK
open import LoopK-PT-assoc-aux

-- associativity condition for pseudotransformation from identity to Ω ∘ K₂

module LoopK-PT-assoc where

module _ {i j k} {G₁ : Type i} {G₂ : Type j} {G₃ : Type k}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}}
  (φ₁@(cohgrphom _ {{σ₁}}) : CohGrpHom {{η₁}} {{η₂}}) (φ₂@(cohgrphom _ {{σ₂}}) : CohGrpHom {{η₂}} {{η₃}}) where
  
  open LKPT-assoc φ₁ φ₂

  abstract
    LoopK-coher-assoc :
      ! (natiso2G-to-== (sq-ΩK (φ₂ ∘2Gσ φ₁))) ∙
      ap (λ m → m ∘2G K₂-loopmap G₁)
        (ap Loop2Grp-map (⊙-comp-to-== (K₂-map-∘ σ₁ σ₂)) ∙
        natiso2G-to-== (Loop2Grp-map-∘ (K₂-map⊙ σ₂) (K₂-map⊙ σ₁))) ∙
      ! (natiso2G-to-==
          (assoc-wksgrphom (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))) (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₁))) (grphom-forg (K₂-loopmap G₁)))) ∙
      ap (λ m → Loop2Grp-map (K₂-map⊙ σ₂) ∘2G m) (natiso2G-to-== (sq-ΩK σ₁)) ∙
      natiso2G-to-==
        (assoc-wksgrphom (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))) (grphom-forg (K₂-loopmap G₂)) (grphom-forg φ₁)) ∙
      ap (λ m → m ∘2G φ₁) (natiso2G-to-== (sq-ΩK σ₂)) ∙
      ! (natiso2G-to-== {μ = K₂-loopmap G₃ ∘2G φ₂ ∘2G φ₁} {ν = (K₂-loopmap G₃ ∘2G φ₂) ∘2G φ₁}
          (assoc-wksgrphom (grphom-forg (K₂-loopmap G₃)) (grphom-forg φ₂) (grphom-forg φ₁))) ∙
      idp
        ==
      idp
    LoopK-coher-assoc = =ₛ-out (LoopK-coher-assoc0 ∙ₛ (LoopK-coher-assoc1 ∙ₛ (LoopK-coher-assoc2 ∙ₛ LoopK-coher-assoc3)))
