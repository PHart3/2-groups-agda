{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=2 #-}

open import lib.Basics
open import 2Magma
open import 2Grp
open import Delooping
open import KFunctor

module apK-aux0 where

open CohGrp {{...}}

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {f₁ f₂ : G₁ → G₂}
  {σ₁ : WkMagHomStr f₁} {σ₂ : WkMagHomStr f₂} where

  open WkMagNatIso

  module _ (iso : WkMagNatIso (maghom-forg (cohmaghom f₁ {{σ₁}})) (maghom-forg (cohmaghom f₂ {{σ₂}})))
    (x y : G₁) where

    apK₂-coher0 = 
      ∙-ap (fst (K₂-map⊙ σ₁)) (loop G₁ x) (loop G₁ y) ◃∙
      ap (ap (fst (K₂-map⊙ σ₁))) (loop-comp G₁ x y) ◃∙
      (K₂-map-β-pts σ₁ (mu x y) ∙ ap (loop G₂) (θ iso (mu x y)) ∙ ! (K₂-map-β-pts σ₂ (mu x y))) ◃∎
        =ₑ⟨ 2 & 1 & (K₂-map-β-pts σ₁ (mu x y) ◃∙ ap (loop G₂) (θ iso (mu x y)) ◃∙ ! (K₂-map-β-pts σ₂ (mu x y)) ◃∎) % =ₛ-in idp ⟩
      ∙-ap (fst (K₂-map⊙ σ₁)) (loop G₁ x) (loop G₁ y) ◃∙
      ap (ap (fst (K₂-map⊙ σ₁))) (loop-comp G₁ x y) ◃∙
      K₂-map-β-pts σ₁ (mu x y) ◃∙
      ap (loop G₂) (θ iso (mu x y)) ◃∙
      ! (K₂-map-β-pts σ₂ (mu x y)) ◃∎ ∎ₛ
