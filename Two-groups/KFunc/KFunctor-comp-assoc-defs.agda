{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import lib.Basics
open import 2Magma
open import 2Grp
open import Delooping
open import KFunctor
open import KFunctor-comp
open import apK

module KFunctor-comp-assoc-defs
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {G₁ : Type ℓ₁} {G₂ : Type ℓ₂} {G₃ : Type ℓ₃} {G₄ : Type ℓ₄}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}} {{η₄ : CohGrp G₄}}
  {f₁ : G₁ → G₂} (σ₁ : WkMagHomStr f₁) {f₂ : G₂ → G₃}
  (σ₂ : WkMagHomStr f₂) {f₃ : G₃ → G₄} (σ₃ : WkMagHomStr f₃) where

  m₁ = cohmaghom f₁ {{σ₁}}
  m₂ = cohmaghom f₂ {{σ₂}}
  m₃ = cohmaghom f₃ {{σ₃}}

  ν₁ =
    λ v →
      K₂-map-β-pts (m₂ ∘2Mσ m₁) v ∙
      ! (K₂-map-β-pts σ₂ (f₁ v)) ∙
      ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ v)) ∙
      ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ v)
  ν₂ =
    λ v →
      K₂-map-β-pts (m₃ ∘2Mσ (m₂ ∘2M m₁)) v ∙
      ! (K₂-map-β-pts σ₃ ((f₂ ∘ f₁) v)) ∙
      ! (ap (ap (K₂-map σ₃)) (K₂-map-β-pts (m₂ ∘2Mσ m₁) v)) ∙
      ∘-ap (K₂-map σ₃) (K₂-map (m₂ ∘2Mσ m₁)) (loop G₁ v)
  ν₃ =
    λ v →
      K₂-map-β-pts (m₃ ∘2Mσ (m₂ ∘2M m₁)) v ∙
      ! (K₂-map-β-pts ((m₃ ∘2M m₂) ∘2Mσ m₁) v)
  ν₄ =
    λ v →
      K₂-map-β-pts ((m₃ ∘2M m₂) ∘2Mσ m₁) v ∙
      ! (K₂-map-β-pts (m₃ ∘2Mσ m₂) (f₁ v)) ∙
      ! (ap (ap (K₂-map (m₃ ∘2Mσ m₂))) (K₂-map-β-pts σ₁ v)) ∙
      ∘-ap (K₂-map (m₃ ∘2Mσ m₂)) (K₂-map σ₁) (loop G₁ v)
  ν₅ =
    λ v →
      K₂-map-β-pts (m₃ ∘2Mσ m₂) v ∙
      ! (K₂-map-β-pts σ₃ (f₂ v)) ∙
      ! (ap (ap (K₂-map σ₃)) (K₂-map-β-pts σ₂ v)) ∙
      ∘-ap (K₂-map σ₃) (K₂-map σ₂) (loop G₂ v)

  module _ (x : G₁) where

    δ₁ =
      K₂-map-β-pts (m₂ ∘2Mσ m₁) x ◃∙
      ! (K₂-map-β-pts σ₂ (f₁ x)) ◃∙
      ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ x)) ◃∙
      ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x) ◃∎
    δ₂ =
      K₂-map-β-pts (m₃ ∘2Mσ (m₂ ∘2M m₁)) x ◃∙
      ! (K₂-map-β-pts σ₃ ((f₂ ∘ f₁) x)) ◃∙
      ! (ap (ap (K₂-map σ₃)) (K₂-map-β-pts (m₂ ∘2Mσ m₁) x)) ◃∙
      ∘-ap (K₂-map σ₃) (K₂-map (m₂ ∘2Mσ m₁)) (loop G₁ x) ◃∎
    δ₃ =
      K₂-map-β-pts (m₃ ∘2Mσ (m₂ ∘2M m₁)) x ◃∙
      ! (K₂-map-β-pts ((m₃ ∘2M m₂) ∘2Mσ m₁) x) ◃∎
    δ₄ =
      K₂-map-β-pts ((m₃ ∘2M m₂) ∘2Mσ m₁) x ◃∙
      ! (K₂-map-β-pts (m₃ ∘2Mσ m₂) (f₁ x)) ◃∙
      ! (ap (ap (K₂-map (m₃ ∘2Mσ m₂))) (K₂-map-β-pts σ₁ x)) ◃∙
      ∘-ap (K₂-map (m₃ ∘2Mσ m₂)) (K₂-map σ₁) (loop G₁ x) ◃∎
    δ₅ =
      ap (ap (K₂-map (m₃ ∘2Mσ m₂))) (K₂-map-β-pts σ₁ x) ◃∙
      K₂-map-β-pts (m₃ ∘2Mσ m₂) (f₁ x) ◃∙
      ! (K₂-map-β-pts σ₃ (f₂ (f₁ x))) ◃∙
      ! (ap (ap (K₂-map σ₃)) (K₂-map-β-pts σ₂ (f₁ x))) ◃∙
      ∘-ap (K₂-map σ₃) (K₂-map σ₂) (loop G₂ (f₁ x)) ◃∙
      ! (ap (ap (K₂-map σ₃ ∘ K₂-map σ₂)) (K₂-map-β-pts σ₁ x)) ◃∎

{-

KFunc-assoc-coher-out : (x : G₁) →
  hmtpy-nat-∙'
  (λ z →
     ! (ap (K₂-map σ₃)
       (K₂-∼-ind (map₁-∘ σ₁ σ₂) (map₂-∘ σ₁ σ₂) idp
         ν₁
       _ z))
     ∙
     ! (K₂-∼-ind (map₁-∘ (m₂ ∘2Gσ m₁) σ₃) (map₂-∘ (m₂ ∘2Gσ m₁) σ₃) idp
         ν₂
         _ z)
     ∙
     K₂-∼-ind (K₂-map (m₃ ∘2Gσ (m₂ ∘2Gσ m₁))) (K₂-map ((m₃ ∘2Gσ m₂) ∘2Gσ m₁)) idp
       ν₃
       _ z
     ∙
     K₂-∼-ind (map₁-∘ σ₁ (m₃ ∘2Gσ m₂)) (map₂-∘ σ₁ (m₃ ∘2Gσ m₂)) idp
       ν₄
      _ z
     ∙
     K₂-∼-ind (map₁-∘ σ₂ σ₃) (map₂-∘ σ₂ σ₃) idp
       ν₅
       _ (K₂-map σ₁ z))
  (loop G₁ x)
    ==
  hmtpy-nat-∙' (λ z → idp) (loop G₁ x)

-}
