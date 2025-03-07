{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import 2Magma
open import 2MagMap
open import 2Grp
open import Delooping
open import KFunctor
open import KFunctor-comp

module KFunctor-comp-assoc-defs2
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {G₁ : Type ℓ₁} {G₂ : Type ℓ₂} {G₃ : Type ℓ₃} {G₄ : Type ℓ₄}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}} {{η₄ : CohGrp G₄}}
  {f₁ : G₁ → G₂} (σ₁ : WkMagHomStr f₁) {f₂ : G₂ → G₃}
  (σ₂ : WkMagHomStr f₂) {f₃ : G₃ → G₄} (σ₃ : WkMagHomStr f₃) (x : G₁) where

  open import KFunctor-comp-assoc-defs σ₁ σ₂ σ₃

  Λ₁ = 
    idp ◃∙
    ! (ap (λ q → q) (ap (λ q → q) (∘-ap (K₂-map σ₃) (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ x)))) ◃∙
    idp ◃∙
    ! (ap (ap (K₂-map σ₃)) (∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x))) ◃∙
    ! (ap (ap (K₂-map σ₃)) (! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ x)))) ◃∙
    ! (ap (ap (K₂-map σ₃)) (! (K₂-map-β-pts σ₂ (f₁ x)))) ◃∙
    ! (ap (ap (K₂-map σ₃)) (K₂-map-β-pts (m₂ ∘2Mσ m₁) x)) ◃∙
    ! (ap (λ q → q) (ap-∘ (K₂-map σ₃) (K₂-map (m₂ ∘2Mσ m₁)) (loop G₁ x))) ◃∙
    idp ◃∙
    ! (ap (λ q → q) (∘-ap (K₂-map σ₃) (K₂-map (m₂ ∘2Mσ m₁)) (loop G₁ x))) ◃∙
    ! (ap (λ q → q) (! (ap (ap (K₂-map σ₃)) (K₂-map-β-pts (m₂ ∘2Mσ m₁) x)))) ◃∙
    ! (ap (λ q → q) (! (K₂-map-β-pts σ₃ ((f₂ ∘ f₁) x)))) ◃∙
    ! (ap (λ q → q) (K₂-map-β-pts (m₃ ∘2Mσ (m₂ ∘2M m₁)) x)) ◃∙
    ap (λ q → q) (K₂-map-β-pts (m₃ ∘2Mσ (m₂ ∘2M m₁)) x) ◃∙
    ap (λ q → q) (! (K₂-map-β-pts ((m₃ ∘2M m₂) ∘2Mσ m₁) x)) ◃∙
    ap (λ q → q) (K₂-map-β-pts ((m₃ ∘2M m₂) ∘2Mσ m₁) x) ◃∙
    ap (λ q → q) (! (K₂-map-β-pts (m₃ ∘2Mσ m₂) (f₁ x))) ◃∙
    ap (λ q → q) (! (ap (ap (K₂-map (m₃ ∘2Mσ m₂))) (K₂-map-β-pts σ₁ x))) ◃∙
    ap (λ q → q) (∘-ap (K₂-map (m₃ ∘2Mσ m₂)) (K₂-map σ₁) (loop G₁ x)) ◃∙
    ap (λ q → q) (ap-∘ (K₂-map (m₃ ∘2Mσ m₂)) (K₂-map σ₁) (loop G₁ x)) ◃∙
    ap (λ q → q) (ap (ap (K₂-map (m₃ ∘2Mσ m₂))) (K₂-map-β-pts σ₁ x)) ◃∙
    ap (λ q → q) (K₂-map-β-pts (m₃ ∘2Mσ m₂) (f₁ x)) ◃∙
    ap (λ q → q) (! (K₂-map-β-pts σ₃ (f₂ (f₁ x)))) ◃∙
    ap (λ q → q) (! (ap (ap (K₂-map σ₃)) (K₂-map-β-pts σ₂ (f₁ x)))) ◃∙
    ap (λ q → q) (∘-ap (K₂-map σ₃) (K₂-map σ₂) (loop G₂ (f₁ x))) ◃∙
    ap (λ q → q) (! (ap (ap (K₂-map σ₃ ∘ K₂-map σ₂)) (K₂-map-β-pts σ₁ x))) ◃∙
    ap (λ q → q) (ap (λ q → q) (∘-ap (K₂-map σ₃ ∘ K₂-map σ₂) (K₂-map σ₁) (loop G₁ x))) ◃∙
    idp ◃∙
    idp ◃∙
    idp ◃∙
    idp ◃∎

  Λ₂ = 
    idp ◃∙
    ! (ap (λ q → q) (ap (λ q → q) (∘-ap (K₂-map σ₃) (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ x)))) ◃∙
    idp ◃∙
    ! (ap (ap (K₂-map σ₃)) (∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x))) ◃∙
    ! (ap (ap (K₂-map σ₃)) (! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ x)))) ◃∙
    ! (ap (ap (K₂-map σ₃)) (! (K₂-map-β-pts σ₂ (f₁ x)))) ◃∙
    idp ◃∙
    ! (ap (λ q → q) (! (K₂-map-β-pts σ₃ ((f₂ ∘ f₁) x)))) ◃∙
    ! (ap (λ q → q) (K₂-map-β-pts (m₃ ∘2Mσ (m₂ ∘2M m₁)) x)) ◃∙
    ap (λ q → q) (K₂-map-β-pts (m₃ ∘2Mσ (m₂ ∘2M m₁)) x) ◃∙
    ap (λ q → q) (! (K₂-map-β-pts ((m₃ ∘2M m₂) ∘2Mσ m₁) x)) ◃∙
    ap (λ q → q) (K₂-map-β-pts ((m₃ ∘2M m₂) ∘2Mσ m₁) x) ◃∙
    ap (λ q → q) (! (K₂-map-β-pts (m₃ ∘2Mσ m₂) (f₁ x))) ◃∙
    ap (λ q → q) (! (ap (ap (K₂-map (m₃ ∘2Mσ m₂))) (K₂-map-β-pts σ₁ x))) ◃∙
    ap (λ q → q) (∘-ap (K₂-map (m₃ ∘2Mσ m₂)) (K₂-map σ₁) (loop G₁ x)) ◃∙
    ap (λ q → q) (ap-∘ (K₂-map (m₃ ∘2Mσ m₂)) (K₂-map σ₁) (loop G₁ x)) ◃∙
    ap (λ q → q) (ap (ap (K₂-map (m₃ ∘2Mσ m₂))) (K₂-map-β-pts σ₁ x)) ◃∙
    ap (λ q → q) (K₂-map-β-pts (m₃ ∘2Mσ m₂) (f₁ x)) ◃∙
    ap (λ q → q) (! (K₂-map-β-pts σ₃ (f₂ (f₁ x)))) ◃∙
    ap (λ q → q) (! (ap (ap (K₂-map σ₃)) (K₂-map-β-pts σ₂ (f₁ x)))) ◃∙
    ap (λ q → q) (∘-ap (K₂-map σ₃) (K₂-map σ₂) (loop G₂ (f₁ x))) ◃∙
    ap (λ q → q) (! (ap (ap (K₂-map σ₃ ∘ K₂-map σ₂)) (K₂-map-β-pts σ₁ x))) ◃∙
    ap (λ q → q) (ap (λ q → q) (∘-ap (K₂-map σ₃ ∘ K₂-map σ₂) (K₂-map σ₁) (loop G₁ x))) ◃∙
    idp ◃∙
    idp ◃∙
    idp ◃∙
    idp ◃∎

  Λ₃ = 
    idp ◃∙
    ! (ap (λ q → q) (ap (λ q → q) (∘-ap (K₂-map σ₃) (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ x)))) ◃∙
    idp ◃∙
    ! (ap (ap (K₂-map σ₃)) (∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x))) ◃∙
    ! (ap (ap (K₂-map σ₃)) (! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ x)))) ◃∙
    ! (ap (ap (K₂-map σ₃)) (! (K₂-map-β-pts σ₂ (f₁ x)))) ◃∙
    idp ◃∙
    ! (ap (λ q → q) (! (K₂-map-β-pts σ₃ ((f₂ ∘ f₁) x)))) ◃∙
    idp ◃∙
    ap (λ q → q) (! (K₂-map-β-pts ((m₃ ∘2M m₂) ∘2Mσ m₁) x)) ◃∙
    ap (λ q → q) (K₂-map-β-pts ((m₃ ∘2M m₂) ∘2Mσ m₁) x) ◃∙
    ap (λ q → q) (! (K₂-map-β-pts (m₃ ∘2Mσ m₂) (f₁ x))) ◃∙
    ap (λ q → q) (! (ap (ap (K₂-map (m₃ ∘2Mσ m₂))) (K₂-map-β-pts σ₁ x))) ◃∙
    ap (λ q → q) (∘-ap (K₂-map (m₃ ∘2Mσ m₂)) (K₂-map σ₁) (loop G₁ x)) ◃∙
    ap (λ q → q) (ap-∘ (K₂-map (m₃ ∘2Mσ m₂)) (K₂-map σ₁) (loop G₁ x)) ◃∙
    ap (λ q → q) (ap (ap (K₂-map (m₃ ∘2Mσ m₂))) (K₂-map-β-pts σ₁ x)) ◃∙
    ap (λ q → q) (K₂-map-β-pts (m₃ ∘2Mσ m₂) (f₁ x)) ◃∙
    ap (λ q → q) (! (K₂-map-β-pts σ₃ (f₂ (f₁ x)))) ◃∙
    ap (λ q → q) (! (ap (ap (K₂-map σ₃)) (K₂-map-β-pts σ₂ (f₁ x)))) ◃∙
    ap (λ q → q) (∘-ap (K₂-map σ₃) (K₂-map σ₂) (loop G₂ (f₁ x))) ◃∙
    ap (λ q → q) (! (ap (ap (K₂-map σ₃ ∘ K₂-map σ₂)) (K₂-map-β-pts σ₁ x))) ◃∙
    ap (λ q → q) (ap (λ q → q) (∘-ap (K₂-map σ₃ ∘ K₂-map σ₂) (K₂-map σ₁) (loop G₁ x))) ◃∙
    idp ◃∙
    idp ◃∙
    idp ◃∙
    idp ◃∎

  Λ₄ = 
    idp ◃∙
    ! (ap (λ q → q) (ap (λ q → q) (∘-ap (K₂-map σ₃) (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ x)))) ◃∙
    idp ◃∙
    ! (ap (ap (K₂-map σ₃)) (∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x))) ◃∙
    ! (ap (ap (K₂-map σ₃)) (! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ x)))) ◃∙
    ! (ap (ap (K₂-map σ₃)) (! (K₂-map-β-pts σ₂ (f₁ x)))) ◃∙
    idp ◃∙
    ! (ap (λ q → q) (! (K₂-map-β-pts σ₃ (f₂ (f₁ x))))) ◃∙
    idp ◃∙
    ap (λ q → q) (! (K₂-map-β-pts (m₃ ∘2Mσ m₂) (f₁ x))) ◃∙
    ap (λ q → q) (! (ap (ap (K₂-map (m₃ ∘2Mσ m₂))) (K₂-map-β-pts σ₁ x))) ◃∙
    ap (λ q → q) (∘-ap (K₂-map (m₃ ∘2Mσ m₂)) (K₂-map σ₁) (loop G₁ x)) ◃∙
    ap (λ q → q) (ap-∘ (K₂-map (m₃ ∘2Mσ m₂)) (K₂-map σ₁) (loop G₁ x)) ◃∙
    ap (λ q → q) (ap (ap (K₂-map (m₃ ∘2Mσ m₂))) (K₂-map-β-pts σ₁ x)) ◃∙
    ap (λ q → q) (K₂-map-β-pts (m₃ ∘2Mσ m₂) (f₁ x)) ◃∙
    ap (λ q → q) (! (K₂-map-β-pts σ₃ (f₂ (f₁ x)))) ◃∙
    ap (λ q → q) (! (ap (ap (K₂-map σ₃)) (K₂-map-β-pts σ₂ (f₁ x)))) ◃∙
    ap (λ q → q) (∘-ap (K₂-map σ₃) (K₂-map σ₂) (loop G₂ (f₁ x))) ◃∙
    ap (λ q → q) (! (ap (ap (K₂-map σ₃ ∘ K₂-map σ₂)) (K₂-map-β-pts σ₁ x))) ◃∙
    ap (λ q → q) (ap (λ q → q) (∘-ap (K₂-map σ₃ ∘ K₂-map σ₂) (K₂-map σ₁) (loop G₁ x))) ◃∙
    idp ◃∙
    idp ◃∙
    idp ◃∙
    idp ◃∎

  Λ₅ = 
    idp ◃∙
    ! (ap (λ q → q) (ap (λ q → q) (∘-ap (K₂-map σ₃) (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ x)))) ◃∙
    idp ◃∙
    ! (ap (ap (K₂-map σ₃)) (∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x))) ◃∙
    ! (ap (ap (K₂-map σ₃)) (! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ x)))) ◃∙
    ! (ap (ap (K₂-map σ₃)) (! (K₂-map-β-pts σ₂ (f₁ x)))) ◃∙
    idp ◃∙
    ! (ap (λ q → q) (! (K₂-map-β-pts σ₃ (f₂ (f₁ x))))) ◃∙
    idp ◃∙
    ap (λ q → q) (! (K₂-map-β-pts (m₃ ∘2Mσ m₂) (f₁ x))) ◃∙
    idp ◃∙
    ap (λ q → q) (K₂-map-β-pts (m₃ ∘2Mσ m₂) (f₁ x)) ◃∙
    ap (λ q → q) (! (K₂-map-β-pts σ₃ (f₂ (f₁ x)))) ◃∙
    ap (λ q → q) (! (ap (ap (K₂-map σ₃)) (K₂-map-β-pts σ₂ (f₁ x)))) ◃∙
    ap (λ q → q) (∘-ap (K₂-map σ₃) (K₂-map σ₂) (loop G₂ (f₁ x))) ◃∙
    ap (λ q → q) (! (ap (ap (K₂-map σ₃ ∘ K₂-map σ₂)) (K₂-map-β-pts σ₁ x))) ◃∙
    ap (λ q → q) (ap (λ q → q) (∘-ap (K₂-map σ₃ ∘ K₂-map σ₂) (K₂-map σ₁) (loop G₁ x))) ◃∙
    idp ◃∙
    idp ◃∙
    idp ◃∙
    idp ◃∎

  Λ₆ = 
    idp ◃∙
    ! (ap (λ q → q) (ap (λ q → q) (∘-ap (K₂-map σ₃) (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ x)))) ◃∙
    idp ◃∙
    ! (ap (ap (K₂-map σ₃)) (∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x))) ◃∙
    ! (ap (ap (K₂-map σ₃)) (! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ x)))) ◃∙
    ! (ap (ap (K₂-map σ₃)) (! (K₂-map-β-pts σ₂ (f₁ x)))) ◃∙
    idp ◃∙
    ! (ap (λ q → q) (! (K₂-map-β-pts σ₃ (f₂ (f₁ x))))) ◃∙
    idp ◃∙
    ap (λ q → q) (! (K₂-map-β-pts σ₃ (f₂ (f₁ x)))) ◃∙
    ap (λ q → q) (! (ap (ap (K₂-map σ₃)) (K₂-map-β-pts σ₂ (f₁ x)))) ◃∙
    ap (λ q → q) (∘-ap (K₂-map σ₃) (K₂-map σ₂) (loop G₂ (f₁ x))) ◃∙
    ap (λ q → q) (! (ap (ap (K₂-map σ₃ ∘ K₂-map σ₂)) (K₂-map-β-pts σ₁ x))) ◃∙
    ap (λ q → q) (ap (λ q → q) (∘-ap (K₂-map σ₃ ∘ K₂-map σ₂) (K₂-map σ₁) (loop G₁ x))) ◃∙
    idp ◃∙
    idp ◃∙
    idp ◃∙
    idp ◃∎

  Λ₇ = 
    idp ◃∙
    ! (ap (λ q → q) (ap (λ q → q) (∘-ap (K₂-map σ₃) (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ x)))) ◃∙
    idp ◃∙
    ! (ap (ap (K₂-map σ₃)) (∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x))) ◃∙
    ! (ap (ap (K₂-map σ₃)) (! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ x)))) ◃∙
    ! (ap (ap (K₂-map σ₃)) (! (K₂-map-β-pts σ₂ (f₁ x)))) ◃∙
    idp ◃∙
    ap (λ q → q) (! (ap (ap (K₂-map σ₃)) (K₂-map-β-pts σ₂ (f₁ x)))) ◃∙
    ap (λ q → q) (∘-ap (K₂-map σ₃) (K₂-map σ₂) (loop G₂ (f₁ x))) ◃∙
    ap (λ q → q) (! (ap (ap (K₂-map σ₃ ∘ K₂-map σ₂)) (K₂-map-β-pts σ₁ x))) ◃∙
    ap (λ q → q) (ap (λ q → q) (∘-ap (K₂-map σ₃ ∘ K₂-map σ₂) (K₂-map σ₁) (loop G₁ x))) ◃∙
    idp ◃∙
    idp ◃∙
    idp ◃∙
    idp ◃∎

  Λ₈ = 
    idp ◃∙
    ! (ap (λ q → q) (ap (λ q → q) (∘-ap (K₂-map σ₃) (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ x)))) ◃∙
    idp ◃∙
    ! (ap (ap (K₂-map σ₃)) (∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x))) ◃∙
    ! (ap (ap (K₂-map σ₃)) (! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ x)))) ◃∙
    idp ◃∙
    ap (λ q → q) (∘-ap (K₂-map σ₃) (K₂-map σ₂) (loop G₂ (f₁ x))) ◃∙
    ap (λ q → q) (! (ap (ap (K₂-map σ₃ ∘ K₂-map σ₂)) (K₂-map-β-pts σ₁ x))) ◃∙
    ap (λ q → q) (ap (λ q → q) (∘-ap (K₂-map σ₃ ∘ K₂-map σ₂) (K₂-map σ₁) (loop G₁ x))) ◃∙
    idp ◃∙
    idp ◃∙
    idp ◃∙
    idp ◃∎

  Λ₉ = 
    idp ◃∙
    ! (ap (λ q → q) (ap (λ q → q) (∘-ap (K₂-map σ₃) (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ x)))) ◃∙
    idp ◃∙
    ! (ap (ap (K₂-map σ₃)) (∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x))) ◃∙
    ∘-ap (K₂-map σ₃) (K₂-map σ₂) (ap (K₂-map σ₁) (loop G₁ x)) ◃∙
    ap (λ q → q) (ap (λ q → q) (∘-ap (K₂-map σ₃ ∘ K₂-map σ₂) (K₂-map σ₁) (loop G₁ x))) ◃∙
    idp ◃∙
    idp ◃∙
    idp ◃∙
    idp ◃∎
