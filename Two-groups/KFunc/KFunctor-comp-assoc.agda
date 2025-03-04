{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import 2Magma
open import 2MagMap
open import 2Grp
open import K-hom2-ind
open import KFunctor
open import KFunctor-comp
open import apK

module KFunctor-comp-assoc where

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {G₁ : Type ℓ₁} {G₂ : Type ℓ₂} {G₃ : Type ℓ₃} {G₄ : Type ℓ₄}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}} {{η₄ : CohGrp G₄}}
  {f₁ : G₁ → G₂} (σ₁ : WkMagHomStr f₁) {f₂ : G₂ → G₃}
  (σ₂ : WkMagHomStr f₂) {f₃ : G₃ → G₄} (σ₃ : WkMagHomStr f₃)  where

  m₁ = cohmaghom f₁ {{σ₁}}
  m₂ = cohmaghom f₂ {{σ₂}}
  m₃ = cohmaghom f₃ {{σ₃}}

  abstract
    KFunc-assoc :
      !-⊙∼ (⊙∘-post (K₂-map⊙ σ₃) (K₂-map-∘ σ₁ σ₂)) ∙⊙∼
      !-⊙∼ (K₂-map-∘ (m₂ ∘2Mσ m₁) σ₃) ∙⊙∼
      apK₂ (assoc-wkmaghom (maghom-forg m₃) (maghom-forg m₂) (maghom-forg m₁)) ∙⊙∼
      K₂-map-∘ σ₁ (m₃ ∘2Mσ m₂) ∙⊙∼
      ⊙∘-pre (K₂-map⊙ σ₁) (K₂-map-∘ σ₂ σ₃)
        ⊙→∼
      ⊙∘-assoc-comp (K₂-map⊙ σ₃) (K₂-map⊙ σ₂) (K₂-map⊙ σ₁)
    fst KFunc-assoc = K₂-∼∼-ind idp {!!} -- KFunc-assoc-coher-out
    snd KFunc-assoc = =ₛ-in idp

{-

KFunc-assoc-coher-out : (x : G₁) →
  hmtpy-nat-∙'
  (λ z →
     ! (ap (K₂-map σ₃)
       (K₂-∼-ind (map₁-∘ σ₁ σ₂) (map₂-∘ σ₁ σ₂) idp
         (λ v →
           K₂-map-β-pts (m₂ ∘2Wσ m₁) v ∙
           ! (K₂-map-β-pts σ₂ (f₁ v)) ∙
           ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ v)) ∙
           ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ v))
       _ z))
     ∙
     ! (K₂-∼-ind (map₁-∘ (m₂ ∘2Gσ m₁) σ₃) (map₂-∘ (m₂ ∘2Gσ m₁) σ₃) idp
         (λ v →
           K₂-map-β-pts (m₃ ∘2Gσ (m₂ ∘2Gσ m₁)) v ∙
           ! (K₂-map-β-pts σ₃ ((f₂ ∘ f₁) v)) ∙
           ! (ap (ap (K₂-map σ₃)) (K₂-map-β-pts (m₂ ∘2Gσ m₁) v)) ∙
           ∘-ap (K₂-map σ₃) (K₂-map (m₂ ∘2Gσ m₁)) (loop G₁ v))
         _ z)
     ∙
     K₂-∼-ind (K₂-map (m₃ ∘2Gσ (m₂ ∘2Gσ m₁))) (K₂-map ((m₃ ∘2Gσ m₂) ∘2Gσ m₁)) idp
       (λ v →
         K₂-map-β-pts (m₃ ∘2Gσ (m₂ ∘2Gσ m₁)) v ∙
         ! (K₂-map-β-pts ((m₃ ∘2Gσ m₂) ∘2Gσ m₁) v))
       _ z
     ∙
     K₂-∼-ind (map₁-∘ σ₁ (m₃ ∘2Gσ m₂)) (map₂-∘ σ₁ (m₃ ∘2Gσ m₂)) idp
       (λ v →
         K₂-map-β-pts ((m₃ ∘2Gσ m₂) ∘2Gσ m₁) v ∙
         ! (K₂-map-β-pts (m₃ ∘2Gσ m₂) (f₁ v)) ∙
         ! (ap (ap (K₂-map (m₃ ∘2Gσ m₂))) (K₂-map-β-pts σ₁ v)) ∙
         ∘-ap (K₂-map (m₃ ∘2Gσ m₂)) (K₂-map σ₁) (loop G₁ v))
      _ z
     ∙
     K₂-∼-ind (map₁-∘ σ₂ σ₃) (map₂-∘ σ₂ σ₃) idp
       (λ v →
         K₂-map-β-pts (m₃ ∘2Gσ m₂) v ∙
         ! (K₂-map-β-pts σ₃ (f₂ v)) ∙
         ! (ap (ap (K₂-map σ₃)) (K₂-map-β-pts σ₂ v)) ∙
         ∘-ap (K₂-map σ₃) (K₂-map σ₂) (loop G₂ v))
       _ (K₂-map σ₁ z))
  (loop G₁ x)
    ==
  hmtpy-nat-∙' (λ z → idp) (loop G₁ x)

-}
