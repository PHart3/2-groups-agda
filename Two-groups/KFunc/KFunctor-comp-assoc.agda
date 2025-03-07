{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import 2Magma
open import 2MagMap
open import 2Grp
open import Delooping
open import K-hom2-ind
open import KFunctor
open import KFunctor-comp
open import apK
open import KFunctor-comp-assoc-aux3

module KFunctor-comp-assoc where

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {G₁ : Type ℓ₁} {G₂ : Type ℓ₂} {G₃ : Type ℓ₃} {G₄ : Type ℓ₄}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}} {{η₄ : CohGrp G₄}}
  {f₁ : G₁ → G₂} (σ₁ : WkMagHomStr f₁) {f₂ : G₂ → G₃}
  (σ₂ : WkMagHomStr f₂) {f₃ : G₃ → G₄} (σ₃ : WkMagHomStr f₃) where

  open import KFunctor-comp-assoc-defs σ₁ σ₂ σ₃

  abstract
    KFunc-assoc :
      !-⊙∼ (⊙∘-post (K₂-map⊙ σ₃) (K₂-map-∘ σ₁ σ₂)) ∙⊙∼
      !-⊙∼ (K₂-map-∘ (m₂ ∘2Mσ m₁) σ₃) ∙⊙∼
      apK₂ (assoc-wkmaghom (maghom-forg m₃) (maghom-forg m₂) (maghom-forg m₁)) ∙⊙∼
      K₂-map-∘ σ₁ (m₃ ∘2Mσ m₂) ∙⊙∼
      ⊙∘-pre (K₂-map⊙ σ₁) (K₂-map-∘ σ₂ σ₃)
        ⊙→∼
      ⊙∘-α-comp (K₂-map⊙ σ₃) (K₂-map⊙ σ₂) (K₂-map⊙ σ₁)
    fst KFunc-assoc = K₂-∼∼-ind (idp {a = idp {a = base G₄}}) KFunc-assoc-coher-out
      where
        open KFCA3 σ₁ σ₂ σ₃
        abstract
          KFunc-assoc-coher-out : (x : G₁) →
            hmtpy-nat-∙'
              (λ z →
                 ! (ap (K₂-map σ₃) (fst (K₂-map-∘ σ₁ σ₂) z)) ∙
                 ! (fst (K₂-map-∘ (m₂ ∘2Mσ m₁) σ₃) z) ∙
                 fst (apK₂ (assoc-wkmaghom (maghom-forg m₃) (maghom-forg m₂) (maghom-forg m₁))) z ∙
                 fst (K₂-map-∘ σ₁ (m₃ ∘2Mσ m₂)) z ∙
                 fst (K₂-map-∘ σ₂ σ₃) (K₂-map σ₁ z))
              (loop G₁ x)
              ==
            hmtpy-nat-∙' (λ z → idp {a = K₂-map σ₃ (K₂-map σ₂ (K₂-map σ₁ z))}) (loop G₁ x)
          KFunc-assoc-coher-out x = =ₛ-out (KFunc-assoc-coher x)
    snd KFunc-assoc = idp
