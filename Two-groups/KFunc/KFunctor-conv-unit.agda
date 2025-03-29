{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.PtdMap-conv
open import 2Grp
open import 2MagMap
open import 2GrpMap
open import KFunctor
open import KFunctor-idf
open import KFunctor-comp
open import apK
open import KFunctor-comp-lunit
open import KFunctor-comp-runit

module KFunctor-conv-unit where

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  {φ@(cohgrphom f {{σ}}) : CohGrpHom {{η₁}} {{η₂}}} where

  abstract
  
    K₂-ρ :
      ap K₂-action-hom (natiso2G-to-== (unit-wkmaghom-r (grphom-forg φ))) ∙
      ⊙-comp-to-== (K₂-map-∘ idf2G σ) ∙
      ap (λ m → K₂-action-hom φ ⊙∘ m) (⊙-comp-to-== (K₂-map-idf {{η₁}}))
        ==
      ⊙-comp-to-== (⊙∘-runit (K₂-action-hom φ))
    K₂-ρ = =ₛ-out $
      ap K₂-action-hom (natiso2G-to-== (unit-wkmaghom-r (grphom-forg φ))) ◃∙
      ⊙-comp-to-== (K₂-map-∘ idf2G σ) ◃∙
      ap (λ m → K₂-action-hom φ ⊙∘ m) (⊙-comp-to-== (K₂-map-idf {{η₁}})) ◃∎
        =ₛ₁⟨ 0 & 1 & apK₂-pres (unit-wkmaghom-r (grphom-forg φ)) ⟩
      ⊙-comp-to-== (apK₂ (unit-wkmaghom-r (grphom-forg φ))) ◃∙
      ⊙-comp-to-== (K₂-map-∘ idf2G σ) ◃∙
      ap (λ m → K₂-action-hom φ ⊙∘ m) (⊙-comp-to-== (K₂-map-idf {{η₁}})) ◃∎
        =ₛ₁⟨ 2 & 1 & ! (whisk⊙-conv-l {f₁ = K₂-action-hom φ} (K₂-map-idf {{η₁}})) ⟩
      ⊙-comp-to-== (apK₂ (unit-wkmaghom-r (grphom-forg φ))) ◃∙
      ⊙-comp-to-== (K₂-map-∘ idf2G σ) ◃∙
      ⊙-comp-to-== (⊙∘-post (K₂-action-hom φ) (K₂-map-idf {{η₁}})) ◃∎
        =ₛ⟨ !ₛ (⊙∘-conv-tri
                 (apK₂ (unit-wkmaghom-r (grphom-forg φ)))
                 (K₂-map-∘ idf2G σ)
                 (⊙∘-post (K₂-action-hom φ) (K₂-map-idf {{η₁}}))) ⟩
      ⊙-comp-to-==
        (apK₂ (unit-wkmaghom-r (grphom-forg φ)) ∙⊙∼
         K₂-map-∘ idf2G σ ∙⊙∼
         ⊙∘-post (K₂-action-hom φ) (K₂-map-idf {{η₁}})) ◃∎
         =ₛ₁⟨ ap ⊙-comp-to-== (⊙→∼-to-== (KFunc-runit σ)) ⟩
      ⊙-comp-to-== (⊙∘-runit (K₂-action-hom φ)) ◃∎ ∎ₛ

    K₂-λ :
      ap K₂-action-hom (natiso2G-to-== (unit-wkmaghom-l (grphom-forg φ))) ∙
      ⊙-comp-to-== (K₂-map-∘ σ idf2G) ∙
      ap (λ m → m ⊙∘ K₂-action-hom φ) (⊙-comp-to-== (K₂-map-idf {{η₂}}))
        ==
      ⊙-comp-to-== (⊙∘-lunit (K₂-action-hom φ))
    K₂-λ = =ₛ-out $
      ap K₂-action-hom (natiso2G-to-== (unit-wkmaghom-l (grphom-forg φ))) ◃∙
      ⊙-comp-to-== (K₂-map-∘ σ idf2G) ◃∙
      ap (λ m → m ⊙∘ K₂-action-hom φ) (⊙-comp-to-== (K₂-map-idf {{η₂}})) ◃∎
          =ₛ₁⟨ 0 & 1 & apK₂-pres (unit-wkmaghom-l (grphom-forg φ)) ⟩
      ⊙-comp-to-== (apK₂ (unit-wkmaghom-l (grphom-forg φ))) ◃∙
      ⊙-comp-to-== (K₂-map-∘ σ idf2G) ◃∙
      ap (λ m → m ⊙∘ K₂-action-hom φ) (⊙-comp-to-== (K₂-map-idf {{η₂}})) ◃∎
        =ₛ₁⟨ 2 & 1 & ! (whisk⊙-conv-r {f₁ = K₂-action-hom φ} (K₂-map-idf {{η₂}})) ⟩
      ⊙-comp-to-== (apK₂ (unit-wkmaghom-l (grphom-forg φ))) ◃∙
      ⊙-comp-to-== (K₂-map-∘ σ idf2G) ◃∙
      ⊙-comp-to-== (⊙∘-pre (K₂-action-hom φ) (K₂-map-idf {{η₂}})) ◃∎
        =ₛ⟨ !ₛ (⊙∘-conv-tri
                 (apK₂ (unit-wkmaghom-l (grphom-forg φ)))
                 (K₂-map-∘ σ idf2G)
                 (⊙∘-pre (K₂-action-hom φ) (K₂-map-idf {{η₂}}))) ⟩
      ⊙-comp-to-==
        (apK₂ (unit-wkmaghom-l (grphom-forg φ)) ∙⊙∼
         K₂-map-∘ σ idf2G ∙⊙∼
         ⊙∘-pre (K₂-action-hom φ) (K₂-map-idf {{η₂}})) ◃∎
         =ₛ₁⟨ ap ⊙-comp-to-== (⊙→∼-to-== (KFunc-lunit σ)) ⟩
      ⊙-comp-to-== (⊙∘-lunit (K₂-action-hom φ)) ◃∎ ∎ₛ
