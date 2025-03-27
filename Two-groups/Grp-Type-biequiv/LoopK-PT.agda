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

  abstract
    LoopK-coher-assoc :
      ! (natiso2G-to-== (sq-ΩK (φ₂ ∘2Gσ φ₁))) ∙
      ap (λ m → m ∘2G K₂-loopmap G₁)
        (ap Loop2Grp-map (⊙-comp-to-== (K₂-map-∘ σ₁ σ₂)) ∙
        natiso2G-to-== (Loop2Grp-map-∘ (K₂-map⊙ σ₂) (K₂-map⊙ σ₁))) ∙
      ! (natiso2G-to-==
          (assoc-wkmaghom (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))) (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₁))) (grphom-forg (K₂-loopmap G₁)))) ∙
      ap (λ m → Loop2Grp-map (K₂-map⊙ σ₂) ∘2G m) (natiso2G-to-== (sq-ΩK σ₁)) ∙
      natiso2G-to-==
        (assoc-wkmaghom (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))) (grphom-forg (K₂-loopmap G₂)) (grphom-forg φ₁)) ∙
      ap (λ m → m ∘2G φ₁) (natiso2G-to-== (sq-ΩK σ₂)) ∙
      ! (natiso2G-to-==
          (assoc-wkmaghom (grphom-forg (K₂-loopmap G₃)) (grphom-forg φ₂) (grphom-forg φ₁))) ∙
      idp
        ==
      idp
    LoopK-coher-assoc = =ₛ-out $
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
      ! (natiso2G-to-==
          (assoc-wkmaghom (grphom-forg (K₂-loopmap G₃)) (grphom-forg φ₂) (grphom-forg φ₁))) ◃∙
      idp ◃∎
        =ₛ₁⟨ 0 & 1 & ! (natiso2G-! (sq-ΩK (φ₂ ∘2Gσ φ₁))) ⟩
      natiso2G-to-== (!ʷ (sq-ΩK (cohgrphom (map φ₂) ∘2Gσ cohgrphom (map φ₁)))) ◃∙
      ap (λ m → m ∘2G K₂-loopmap G₁)
        (ap Loop2Grp-map (⊙-comp-to-== (K₂-map-∘ σ₁ σ₂)) ∙
        natiso2G-to-== (Loop2Grp-map-∘ (K₂-map⊙ σ₂) (K₂-map⊙ σ₁))) ◃∙
      ! (natiso2G-to-==
          (assoc-wkmaghom (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))) (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₁))) (grphom-forg (K₂-loopmap G₁)))) ◃∙
      ap (λ m → Loop2Grp-map (K₂-map⊙ σ₂) ∘2G m) (natiso2G-to-== (sq-ΩK σ₁)) ◃∙
      natiso2G-to-==
        (assoc-wkmaghom (grphom-forg (Loop2Grp-map (K₂-map⊙ σ₂))) (grphom-forg (K₂-loopmap G₂)) (grphom-forg φ₁)) ◃∙
      ap (λ m → m ∘2G φ₁) (natiso2G-to-== (sq-ΩK σ₂)) ◃∙
      ! (natiso2G-to-==
          (assoc-wkmaghom (grphom-forg (K₂-loopmap G₃)) (grphom-forg φ₂) (grphom-forg φ₁))) ◃∙
      idp ◃∎
        =ₛ₁⟨ 2 & 1 & ? ⟩
      ?
