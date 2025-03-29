{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.PtdMap-conv
open import 2MagMap
open import 2Grp
open import 2GrpMap
open import KFunctor
open import KFunctor-comp
open import apK
open import KFunctor-comp-assoc

module KFunctor-conv-assoc where

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {G₁ : Type ℓ₁} {G₂ : Type ℓ₂} {G₃ : Type ℓ₃} {G₄ : Type ℓ₄}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}} {{η₄ : CohGrp G₄}}
  (φ₁@(cohgrphom f₁ {{σ₁}}) : CohGrpHom {{η₁}} {{η₂}})
  (φ₂@(cohgrphom f₂ {{σ₂}}) : CohGrpHom {{η₂}} {{η₃}})
  (φ₃@(cohgrphom f₃ {{σ₃}}) : CohGrpHom {{η₃}} {{η₄}}) where

  abstract
    K₂-α :
      ! (ap (λ m → K₂-action-hom φ₃ ⊙∘ m) (⊙-comp-to-== (K₂-map-∘ σ₁ σ₂))) ∙
      ! (⊙-comp-to-== (K₂-map-∘ (φ₂ ∘2Gσ φ₁) σ₃)) ∙
      ap K₂-action-hom (natiso2G-to-== (assoc-wkmaghom (grphom-forg φ₃) (grphom-forg φ₂) (grphom-forg φ₁))) ∙
      ⊙-comp-to-== (K₂-map-∘ σ₁ (φ₃ ∘2Gσ φ₂)) ∙
      ap (λ m → m ⊙∘ K₂-action-hom φ₁) (⊙-comp-to-== (K₂-map-∘ σ₂ σ₃))
        ==
      ⊙-comp-to-== (⊙∘-α-comp (K₂-action-hom φ₃) (K₂-action-hom φ₂) (K₂-action-hom φ₁))
    K₂-α =  =ₛ-out $
      ! (ap (λ m → K₂-action-hom φ₃ ⊙∘ m) (⊙-comp-to-== (K₂-map-∘ σ₁ σ₂))) ◃∙
      ! (⊙-comp-to-== (K₂-map-∘ (φ₂ ∘2Gσ φ₁) σ₃)) ◃∙
      ap K₂-action-hom (natiso2G-to-== (assoc-wkmaghom (grphom-forg φ₃) (grphom-forg φ₂) (grphom-forg φ₁))) ◃∙
      ⊙-comp-to-== (K₂-map-∘ σ₁ (φ₃ ∘2Gσ φ₂)) ◃∙
      ap (λ m → m ⊙∘ K₂-action-hom φ₁) (⊙-comp-to-== (K₂-map-∘ σ₂ σ₃)) ◃∎
        =ₛ₁⟨ 0 & 1 & ap ! (! (whisk⊙-conv-l {f₁ = K₂-action-hom φ₃} (K₂-map-∘ σ₁ σ₂))) ⟩
      ! (⊙-comp-to-== (⊙∘-post (K₂-action-hom φ₃) (K₂-map-∘ σ₁ σ₂))) ◃∙
      ! (⊙-comp-to-== (K₂-map-∘ (φ₂ ∘2Gσ φ₁) σ₃)) ◃∙
      ap K₂-action-hom (natiso2G-to-== (assoc-wkmaghom (grphom-forg φ₃) (grphom-forg φ₂) (grphom-forg φ₁))) ◃∙
      ⊙-comp-to-== (K₂-map-∘ σ₁ (φ₃ ∘2Gσ φ₂)) ◃∙
      ap (λ m → m ⊙∘ K₂-action-hom φ₁) (⊙-comp-to-== (K₂-map-∘ σ₂ σ₃)) ◃∎
        =ₛ₁⟨ 0 & 1 & ! (!⊙-conv (⊙∘-post (K₂-action-hom φ₃) (K₂-map-∘ σ₁ σ₂))) ⟩
      ⊙-comp-to-== (!-⊙∼ (⊙∘-post (K₂-action-hom φ₃) (K₂-map-∘ σ₁ σ₂))) ◃∙
      ! (⊙-comp-to-== (K₂-map-∘ (φ₂ ∘2Gσ φ₁) σ₃)) ◃∙
      ap K₂-action-hom (natiso2G-to-== (assoc-wkmaghom (grphom-forg φ₃) (grphom-forg φ₂) (grphom-forg φ₁))) ◃∙
      ⊙-comp-to-== (K₂-map-∘ σ₁ (φ₃ ∘2Gσ φ₂)) ◃∙
      ap (λ m → m ⊙∘ K₂-action-hom φ₁) (⊙-comp-to-== (K₂-map-∘ σ₂ σ₃)) ◃∎
        =ₛ₁⟨ 1 & 1 & ! (!⊙-conv (K₂-map-∘ (φ₂ ∘2Gσ φ₁) σ₃)) ⟩
      ⊙-comp-to-== (!-⊙∼ (⊙∘-post (K₂-action-hom φ₃) (K₂-map-∘ σ₁ σ₂))) ◃∙
      ⊙-comp-to-== (!-⊙∼ (K₂-map-∘ (φ₂ ∘2Gσ φ₁) σ₃)) ◃∙
      ap K₂-action-hom (natiso2G-to-== (assoc-wkmaghom (grphom-forg φ₃) (grphom-forg φ₂) (grphom-forg φ₁))) ◃∙
      ⊙-comp-to-== (K₂-map-∘ σ₁ (φ₃ ∘2Gσ φ₂)) ◃∙
      ap (λ m → m ⊙∘ K₂-action-hom φ₁) (⊙-comp-to-== (K₂-map-∘ σ₂ σ₃)) ◃∎
        =ₛ₁⟨ 2 & 1 & apK₂-pres (assoc-wkmaghom (grphom-forg φ₃) (grphom-forg φ₂) (grphom-forg φ₁)) ⟩
      ⊙-comp-to-== (!-⊙∼ (⊙∘-post (K₂-action-hom φ₃) (K₂-map-∘ σ₁ σ₂))) ◃∙
      ⊙-comp-to-== (!-⊙∼ (K₂-map-∘ (φ₂ ∘2Gσ φ₁) σ₃)) ◃∙
      ⊙-comp-to-== (apK₂ (assoc-wkmaghom (grphom-forg φ₃) (grphom-forg φ₂) (grphom-forg φ₁))) ◃∙
      ⊙-comp-to-== (K₂-map-∘ σ₁ (φ₃ ∘2Gσ φ₂)) ◃∙
      ap (λ m → m ⊙∘ K₂-action-hom φ₁) (⊙-comp-to-== (K₂-map-∘ σ₂ σ₃)) ◃∎
        =ₛ₁⟨ 4 & 1 & ! (whisk⊙-conv-r {f₁ = K₂-action-hom φ₁} (K₂-map-∘ σ₂ σ₃)) ⟩
      ⊙-comp-to-== (!-⊙∼ (⊙∘-post (K₂-action-hom φ₃) (K₂-map-∘ σ₁ σ₂))) ◃∙
      ⊙-comp-to-== (!-⊙∼ (K₂-map-∘ (φ₂ ∘2Gσ φ₁) σ₃)) ◃∙
      ⊙-comp-to-== (apK₂ (assoc-wkmaghom (grphom-forg φ₃) (grphom-forg φ₂) (grphom-forg φ₁))) ◃∙
      ⊙-comp-to-== (K₂-map-∘ σ₁ (φ₃ ∘2Gσ φ₂)) ◃∙
      ⊙-comp-to-== (⊙∘-pre (K₂-action-hom φ₁) (K₂-map-∘ σ₂ σ₃)) ◃∎
        =ₛ⟨ ⊙∘-conv-quint
              (!-⊙∼ (⊙∘-post (K₂-action-hom φ₃) (K₂-map-∘ σ₁ σ₂)))
              (!-⊙∼ (K₂-map-∘ (φ₂ ∘2Gσ φ₁) σ₃))
              (apK₂ (assoc-wkmaghom (grphom-forg φ₃) (grphom-forg φ₂) (grphom-forg φ₁)))
              (K₂-map-∘ σ₁ (φ₃ ∘2Gσ φ₂))
              (⊙∘-pre (K₂-action-hom φ₁) (K₂-map-∘ σ₂ σ₃)) ⟩
      ⊙-comp-to-==
        (!-⊙∼ (⊙∘-post (K₂-action-hom φ₃) (K₂-map-∘ σ₁ σ₂)) ∙⊙∼
        !-⊙∼ (K₂-map-∘ (φ₂ ∘2Gσ φ₁) σ₃) ∙⊙∼
        apK₂ (assoc-wkmaghom (grphom-forg φ₃) (grphom-forg φ₂) (grphom-forg φ₁)) ∙⊙∼
        K₂-map-∘ σ₁ (φ₃ ∘2Gσ φ₂) ∙⊙∼
        ⊙∘-pre (K₂-action-hom φ₁) (K₂-map-∘ σ₂ σ₃)) ◃∎
        =ₛ₁⟨ ap ⊙-comp-to-== (⊙→∼-to-== (KFunc-assoc σ₁ σ₂ σ₃)) ⟩
      ⊙-comp-to-== (⊙∘-α-comp (K₂-action-hom φ₃) (K₂-action-hom φ₂) (K₂-action-hom φ₁)) ◃∎ ∎ₛ
