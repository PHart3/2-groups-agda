{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=5 --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.LoopSpace
open import 2Grp
open import 2MagMap
open import 2GrpMap
open import 2GrpMap-conv
open import Hmtpy2Grp
open import Delooping
open import Bicategory
open import 2Grp-bc
open import Ptd-bc
open import KFunctor
open import KFunctor-comp
open import KFunctor-idf
open import LoopFunctor-ap
open import SqLoopK
open import LoopK-ptr-idf
open import LoopK-ptr-comp

-- Pseudotransformation from identity to Ω ∘ K₂

module LoopK-PT where

module _ {i j k} {G₁ : Type i} {G₂ : Type j} {G₃ : Type k}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}}
  (φ₁@(cohgrphom f₁ {{σ₁}}) : CohGrpHom {{η₁}} {{η₂}}) (φ₂@(cohgrphom f₂ {{σ₂}}) : CohGrpHom {{η₂}} {{η₃}}) where

  open CohGrp {{...}}
  open CohGrpHom

  private
    τ₀ =
      ! (natiso2G-to-== (sq-ΩK (φ₂ ∘2Gσ φ₁))) ◃∙
      ap (λ m → m ∘2G K₂-loopmap G₁)
        (ap Loop2Grp-map (⊙-comp-to-== (K₂-map-∘ σ₁ σ₂)) ∙
        natiso2G-to-== (Loop2Grp-map-∘ (K₂-map⊙ σ₂) (K₂-map⊙ σ₁))) ◃∙
      ! (natiso2G-to-==
          (assoc-wkmaghom (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))) (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₁))) (grphom-forg (K₂-loopmap G₁)))) ◃∙
      ap (λ m → Loop2Grp-map (K₂-map⊙ σ₂) ∘2G m) (natiso2G-to-== (sq-ΩK σ₁)) ◃∙
      natiso2G-to-==
        (assoc-wkmaghom (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))) (grphom-forg (K₂-loopmap G₂)) (grphom-forg φ₁)) ◃∙
      ap (λ m → m ∘2G φ₁) (natiso2G-to-== (sq-ΩK σ₂)) ◃∙
      ! (natiso2G-to-== {μ = K₂-loopmap G₃ ∘2G φ₂ ∘2G φ₁} {ν = (K₂-loopmap G₃ ∘2G φ₂) ∘2G φ₁}
          (assoc-wkmaghom (grphom-forg (K₂-loopmap G₃)) (grphom-forg φ₂) (grphom-forg φ₁))) ◃∙
      idp ◃∎
    τ₁ =
      natiso2G-to-== (!ʷ (sq-ΩK (φ₂ ∘2Gσ φ₁))) ◃∙
      ap (λ m → m ∘2G K₂-loopmap G₁)
        (ap Loop2Grp-map (⊙-comp-to-== (K₂-map-∘ σ₁ σ₂)) ∙
        natiso2G-to-== (Loop2Grp-map-∘ (K₂-map⊙ σ₂) (K₂-map⊙ σ₁))) ◃∙
      natiso2G-to-==
        (!ʷ (assoc-wkmaghom (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))) (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₁))) (grphom-forg (K₂-loopmap G₁)))) ◃∙
      ap (λ m → Loop2Grp-map (K₂-map⊙ σ₂) ∘2G m) (natiso2G-to-== (sq-ΩK σ₁)) ◃∙
      natiso2G-to-==
        (assoc-wkmaghom (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))) (grphom-forg (K₂-loopmap G₂)) (grphom-forg φ₁)) ◃∙
      ap (λ m → m ∘2G φ₁) (natiso2G-to-== (sq-ΩK σ₂)) ◃∙
      natiso2G-to-== {μ = (K₂-loopmap G₃ ∘2G φ₂) ∘2G φ₁} {ν = K₂-loopmap G₃ ∘2G φ₂ ∘2G φ₁}
        (!ʷ (assoc-wkmaghom (grphom-forg (K₂-loopmap G₃)) (grphom-forg φ₂) (grphom-forg φ₁))) ◃∙
      idp ◃∎
    τ₂ =
      natiso2G-to-== (!ʷ (sq-ΩK (φ₂ ∘2Gσ φ₁))) ◃∙
      ap (λ m → m ∘2G K₂-loopmap G₁)
        (ap Loop2Grp-map (⊙-comp-to-== (K₂-map-∘ σ₁ σ₂)) ∙
        natiso2G-to-== (Loop2Grp-map-∘ (K₂-map⊙ σ₂) (K₂-map⊙ σ₁))) ◃∙
      natiso2G-to-==
        {μ = (Loop2Grp-map (K₂-map⊙ σ₂) ∘2G Loop2Grp-map (K₂-map⊙ σ₁)) ∘2G K₂-loopmap G₁}
        {ν = Loop2Grp-map (K₂-map⊙ σ₂) ∘2G Loop2Grp-map (K₂-map⊙ σ₁) ∘2G K₂-loopmap G₁}
        (!ʷ (assoc-wkmaghom (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))) (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₁))) (grphom-forg (K₂-loopmap G₁)))) ◃∙
      natiso2G-to-== (natiso-whisk-l {μ = grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))} (sq-ΩK σ₁)) ◃∙
      natiso2G-to-==
        {μ = Loop2Grp-map (K₂-map⊙ σ₂) ∘2G K₂-loopmap G₂ ∘2G φ₁}
        {ν = (Loop2Grp-map (K₂-map⊙ σ₂) ∘2G K₂-loopmap G₂) ∘2G φ₁}
        (assoc-wkmaghom (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))) (grphom-forg (K₂-loopmap G₂)) (grphom-forg φ₁)) ◃∙
      natiso2G-to-== (natiso-whisk-r (sq-ΩK σ₂)) ◃∙
      natiso2G-to-== {μ = (K₂-loopmap G₃ ∘2G φ₂) ∘2G φ₁} {ν = K₂-loopmap G₃ ∘2G φ₂ ∘2G φ₁}
        (!ʷ (assoc-wkmaghom (grphom-forg (K₂-loopmap G₃)) (grphom-forg φ₂) (grphom-forg φ₁))) ◃∙
      idp ◃∎
    τ₃ =
      natiso2G-to-== (!ʷ (sq-ΩK (φ₂ ∘2Gσ φ₁))) ◃∙
      natiso2G-to-==
        {μ = Loop2Grp-map (K₂-map⊙ (φ₂ ∘2Gσ φ₁)) ∘2G K₂-loopmap G₁}
        {ν = Loop2Grp-map (K₂-map⊙ σ₂ ⊙∘ K₂-map⊙ σ₁) ∘2G K₂-loopmap G₁}
        (natiso-whisk-r {μ = grphom-forg (K₂-loopmap G₁)} (Loop2Grp-map-ap (K₂-map-∘ σ₁ σ₂))) ◃∙
      natiso2G-to-== (natiso-whisk-r {μ = grphom-forg (K₂-loopmap G₁)} (Loop2Grp-map-∘ (K₂-map⊙ σ₂) (K₂-map⊙ σ₁))) ◃∙
      natiso2G-to-==
        {μ = (Loop2Grp-map (K₂-map⊙ σ₂) ∘2G Loop2Grp-map (K₂-map⊙ σ₁)) ∘2G K₂-loopmap G₁}
        {ν = Loop2Grp-map (K₂-map⊙ σ₂) ∘2G Loop2Grp-map (K₂-map⊙ σ₁) ∘2G K₂-loopmap G₁}
        (!ʷ (assoc-wkmaghom (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))) (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₁))) (grphom-forg (K₂-loopmap G₁)))) ◃∙
      natiso2G-to-== (natiso-whisk-l {μ = grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))} (sq-ΩK σ₁)) ◃∙
      natiso2G-to-==
        {μ = Loop2Grp-map (K₂-map⊙ σ₂) ∘2G K₂-loopmap G₂ ∘2G φ₁}
        {ν = (Loop2Grp-map (K₂-map⊙ σ₂) ∘2G K₂-loopmap G₂) ∘2G φ₁}
        (assoc-wkmaghom (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))) (grphom-forg (K₂-loopmap G₂)) (grphom-forg φ₁)) ◃∙
      natiso2G-to-== (natiso-whisk-r (sq-ΩK σ₂)) ◃∙
      natiso2G-to-== {μ = (K₂-loopmap G₃ ∘2G φ₂) ∘2G φ₁} {ν = K₂-loopmap G₃ ∘2G φ₂ ∘2G φ₁}
        (!ʷ (assoc-wkmaghom (grphom-forg (K₂-loopmap G₃)) (grphom-forg φ₂) (grphom-forg φ₁))) ◃∙
      idp ◃∎

  abstract
    LoopK-coher-assoc0 : τ₀ =ₛ τ₁
    LoopK-coher-assoc0 =
      τ₀
        =ₛ₁⟨ 0 & 1 & ! (natiso2G-! (sq-ΩK (φ₂ ∘2Gσ φ₁))) ⟩
      natiso2G-to-== (!ʷ (sq-ΩK (φ₂ ∘2Gσ φ₁))) ◃∙
      ap (λ m → m ∘2G K₂-loopmap G₁)
        (ap Loop2Grp-map (⊙-comp-to-== (K₂-map-∘ σ₁ σ₂)) ∙
        natiso2G-to-== (Loop2Grp-map-∘ (K₂-map⊙ σ₂) (K₂-map⊙ σ₁))) ◃∙
      ! (natiso2G-to-==
          (assoc-wkmaghom (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))) (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₁))) (grphom-forg (K₂-loopmap G₁)))) ◃∙
      ap (λ m → Loop2Grp-map (K₂-map⊙ σ₂) ∘2G m) (natiso2G-to-== (sq-ΩK σ₁)) ◃∙
      natiso2G-to-==
        (assoc-wkmaghom (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))) (grphom-forg (K₂-loopmap G₂)) (grphom-forg φ₁)) ◃∙
      ap (λ m → m ∘2G φ₁) (natiso2G-to-== (sq-ΩK σ₂)) ◃∙
      ! (natiso2G-to-== {μ = K₂-loopmap G₃ ∘2G φ₂ ∘2G φ₁} {ν = (K₂-loopmap G₃ ∘2G φ₂) ∘2G φ₁}
          (assoc-wkmaghom (grphom-forg (K₂-loopmap G₃)) (grphom-forg φ₂) (grphom-forg φ₁))) ◃∙
      idp ◃∎
        =ₛ₁⟨ 2 & 1 & ! (natiso2G-! $
          assoc-wkmaghom (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))) (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₁))) (grphom-forg (K₂-loopmap G₁))) ⟩
      natiso2G-to-== (!ʷ (sq-ΩK (φ₂ ∘2Gσ φ₁))) ◃∙
      ap (λ m → m ∘2G K₂-loopmap G₁)
        (ap Loop2Grp-map (⊙-comp-to-== (K₂-map-∘ σ₁ σ₂)) ∙
        natiso2G-to-== (Loop2Grp-map-∘ (K₂-map⊙ σ₂) (K₂-map⊙ σ₁))) ◃∙
      natiso2G-to-==
        (!ʷ (assoc-wkmaghom (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))) (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₁))) (grphom-forg (K₂-loopmap G₁)))) ◃∙
      ap (λ m → Loop2Grp-map (K₂-map⊙ σ₂) ∘2G m) (natiso2G-to-== (sq-ΩK σ₁)) ◃∙
      natiso2G-to-==
        (assoc-wkmaghom (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))) (grphom-forg (K₂-loopmap G₂)) (grphom-forg φ₁)) ◃∙
      ap (λ m → m ∘2G φ₁) (natiso2G-to-== (sq-ΩK σ₂)) ◃∙
      ! (natiso2G-to-== {μ = K₂-loopmap G₃ ∘2G φ₂ ∘2G φ₁} {ν = (K₂-loopmap G₃ ∘2G φ₂) ∘2G φ₁}
          (assoc-wkmaghom (grphom-forg (K₂-loopmap G₃)) (grphom-forg φ₂) (grphom-forg φ₁))) ◃∙
      idp ◃∎
        =ₛ₁⟨ 6 & 1 & ! (natiso2G-! $
          assoc-wkmaghom (grphom-forg (K₂-loopmap G₃)) (grphom-forg φ₂) (grphom-forg φ₁)) ⟩
      τ₁ ∎ₛ

    LoopK-coher-assoc1 : τ₁ =ₛ τ₂
    LoopK-coher-assoc1 = 
      τ₁
        =ₛ₁⟨ 3 & 1 & ! (whisk2G-conv-l (sq-ΩK σ₁)) ⟩
      natiso2G-to-== (!ʷ (sq-ΩK (φ₂ ∘2Gσ φ₁))) ◃∙
      ap (λ m → m ∘2G K₂-loopmap G₁)
        (ap Loop2Grp-map (⊙-comp-to-== (K₂-map-∘ σ₁ σ₂)) ∙
        natiso2G-to-== (Loop2Grp-map-∘ (K₂-map⊙ σ₂) (K₂-map⊙ σ₁))) ◃∙
      natiso2G-to-==
        {μ = (Loop2Grp-map (K₂-map⊙ σ₂) ∘2G Loop2Grp-map (K₂-map⊙ σ₁)) ∘2G K₂-loopmap G₁}
        {ν = Loop2Grp-map (K₂-map⊙ σ₂) ∘2G Loop2Grp-map (K₂-map⊙ σ₁) ∘2G K₂-loopmap G₁}
        (!ʷ (assoc-wkmaghom (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))) (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₁))) (grphom-forg (K₂-loopmap G₁)))) ◃∙
      natiso2G-to-== (natiso-whisk-l {μ = grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))} (sq-ΩK σ₁)) ◃∙
      natiso2G-to-==
        {μ = Loop2Grp-map (K₂-map⊙ σ₂) ∘2G K₂-loopmap G₂ ∘2G φ₁}
        {ν = (Loop2Grp-map (K₂-map⊙ σ₂) ∘2G K₂-loopmap G₂) ∘2G φ₁}
        (assoc-wkmaghom (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))) (grphom-forg (K₂-loopmap G₂)) (grphom-forg φ₁)) ◃∙
      ap (λ m → m ∘2G φ₁) (natiso2G-to-== (sq-ΩK σ₂)) ◃∙
      natiso2G-to-== {μ = (K₂-loopmap G₃ ∘2G φ₂) ∘2G φ₁} {ν = K₂-loopmap G₃ ∘2G φ₂ ∘2G φ₁}
        (!ʷ (assoc-wkmaghom (grphom-forg (K₂-loopmap G₃)) (grphom-forg φ₂) (grphom-forg φ₁))) ◃∙
      idp ◃∎
        =ₛ₁⟨ 5 & 1 & ! (whisk2G-conv-r (sq-ΩK σ₂)) ⟩
      τ₂ ∎ₛ

    LoopK-coher-assoc2 : τ₂ =ₛ τ₃
    LoopK-coher-assoc2 =
      τ₂
        =ₛ⟨ 1 & 1 & ap-∙◃ (λ m → m ∘2G K₂-loopmap G₁)
                      (ap Loop2Grp-map (⊙-comp-to-== (K₂-map-∘ σ₁ σ₂)))
                      (natiso2G-to-== (Loop2Grp-map-∘ (K₂-map⊙ σ₂) (K₂-map⊙ σ₁))) ⟩
      natiso2G-to-== (!ʷ (sq-ΩK (φ₂ ∘2Gσ φ₁))) ◃∙
      ap (λ m → m ∘2G K₂-loopmap G₁) (ap Loop2Grp-map (⊙-comp-to-== (K₂-map-∘ σ₁ σ₂))) ◃∙
      ap (λ m → m ∘2G K₂-loopmap G₁) (natiso2G-to-== (Loop2Grp-map-∘ (K₂-map⊙ σ₂) (K₂-map⊙ σ₁))) ◃∙
      natiso2G-to-==
        {μ = (Loop2Grp-map (K₂-map⊙ σ₂) ∘2G Loop2Grp-map (K₂-map⊙ σ₁)) ∘2G K₂-loopmap G₁}
        {ν = Loop2Grp-map (K₂-map⊙ σ₂) ∘2G Loop2Grp-map (K₂-map⊙ σ₁) ∘2G K₂-loopmap G₁}
        (!ʷ (assoc-wkmaghom (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))) (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₁))) (grphom-forg (K₂-loopmap G₁)))) ◃∙
      natiso2G-to-== (natiso-whisk-l {μ = grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))} (sq-ΩK σ₁)) ◃∙
      natiso2G-to-==
        {μ = Loop2Grp-map (K₂-map⊙ σ₂) ∘2G K₂-loopmap G₂ ∘2G φ₁}
        {ν = (Loop2Grp-map (K₂-map⊙ σ₂) ∘2G K₂-loopmap G₂) ∘2G φ₁}
        (assoc-wkmaghom (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))) (grphom-forg (K₂-loopmap G₂)) (grphom-forg φ₁)) ◃∙
      natiso2G-to-== (natiso-whisk-r (sq-ΩK σ₂)) ◃∙
      natiso2G-to-== {μ = (K₂-loopmap G₃ ∘2G φ₂) ∘2G φ₁} {ν = K₂-loopmap G₃ ∘2G φ₂ ∘2G φ₁}
        (!ʷ (assoc-wkmaghom (grphom-forg (K₂-loopmap G₃)) (grphom-forg φ₂) (grphom-forg φ₁))) ◃∙
      idp ◃∎
        =ₛ₁⟨ 2 & 1 & ! (whisk2G-conv-r (Loop2Grp-map-∘ (K₂-map⊙ σ₂) (K₂-map⊙ σ₁))) ⟩
      natiso2G-to-== (!ʷ (sq-ΩK (φ₂ ∘2Gσ φ₁))) ◃∙
      ap (λ m → m ∘2G K₂-loopmap G₁) (ap Loop2Grp-map (⊙-comp-to-== (K₂-map-∘ σ₁ σ₂))) ◃∙
      natiso2G-to-== (natiso-whisk-r (Loop2Grp-map-∘ (K₂-map⊙ σ₂) (K₂-map⊙ σ₁))) ◃∙
      natiso2G-to-==
        {μ = (Loop2Grp-map (K₂-map⊙ σ₂) ∘2G Loop2Grp-map (K₂-map⊙ σ₁)) ∘2G K₂-loopmap G₁}
        {ν = Loop2Grp-map (K₂-map⊙ σ₂) ∘2G Loop2Grp-map (K₂-map⊙ σ₁) ∘2G K₂-loopmap G₁}
        (!ʷ (assoc-wkmaghom (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))) (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₁))) (grphom-forg (K₂-loopmap G₁)))) ◃∙
      natiso2G-to-== (natiso-whisk-l {μ = grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))} (sq-ΩK σ₁)) ◃∙
      natiso2G-to-==
        {μ = Loop2Grp-map (K₂-map⊙ σ₂) ∘2G K₂-loopmap G₂ ∘2G φ₁}
        {ν = (Loop2Grp-map (K₂-map⊙ σ₂) ∘2G K₂-loopmap G₂) ∘2G φ₁}
        (assoc-wkmaghom (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))) (grphom-forg (K₂-loopmap G₂)) (grphom-forg φ₁)) ◃∙
      natiso2G-to-== (natiso-whisk-r (sq-ΩK σ₂)) ◃∙
      natiso2G-to-== {μ = (K₂-loopmap G₃ ∘2G φ₂) ∘2G φ₁} {ν = K₂-loopmap G₃ ∘2G φ₂ ∘2G φ₁}
        (!ʷ (assoc-wkmaghom (grphom-forg (K₂-loopmap G₃)) (grphom-forg φ₂) (grphom-forg φ₁))) ◃∙
      idp ◃∎
        =ₛ₁⟨ 1 & 1 &
          ap (ap (λ m → m ∘2G K₂-loopmap G₁)) (Ω-fmap-ap-pres (K₂-map-∘ σ₁ σ₂)) ∙
          ! (whisk2G-conv-r (Loop2Grp-map-ap (K₂-map-∘ σ₁ σ₂))) ⟩
      τ₃ ∎ₛ

    -- LoopK-coher-assoc3 : τ₃ =ₛ idp ◃∎
