{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import lib.PathFunctor7
open import 2Semigroup
open import 2SGrpMap
open import 2Grp
open import Delooping
open import KFunctor
open import KFunctor-comp
open import apK
open import KFunctor-comp-assoc-aux0

module KFunctor-comp-assoc-aux1 where

module KFCA1 {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {G₁ : Type ℓ₁} {G₂ : Type ℓ₂} {G₃ : Type ℓ₃} {G₄ : Type ℓ₄}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}} {{η₄ : CohGrp G₄}}
  {f₁ : G₁ → G₂} (σ₁ : WkSGrpHomStr f₁) {f₂ : G₂ → G₃}
  (σ₂ : WkSGrpHomStr f₂) {f₃ : G₃ → G₄} (σ₃ : WkSGrpHomStr f₃) (x : G₁) where

  open import KFunctor-comp-assoc-defs σ₁ σ₂ σ₃
  open import KFunctor-comp-assoc-defs2 σ₁ σ₂ σ₃ x

  open KFCA0 σ₁ σ₂ σ₃ x

  abstract
    KFunc-assoc-coher0 :
      hmtpy-nat-∙'
        (λ z →
           ! (ap (K₂-map σ₃) (fst (K₂-map-∘ σ₁ σ₂) z)) ∙
           ! (fst (K₂-map-∘ (m₂ ∘2Mσ m₁) σ₃) z) ∙
           fst (apK₂ (assoc-wksgrphom (sgrphom-forg m₃) (sgrphom-forg m₂) (sgrphom-forg m₁))) z ∙
           fst (K₂-map-∘ σ₁ (m₃ ∘2Mσ m₂)) z ∙
           fst (K₂-map-∘ σ₂ σ₃) (K₂-map σ₁ z))
        (loop G₁ x) ◃∎
        =ₛ
      Λ₁
    KFunc-assoc-coher0 =
      hnat-∙'-!ap-∙!-∙∙-pre (K₂-map σ₃) (K₂-map σ₁)
        (fst (K₂-map-∘ σ₁ σ₂))
        (fst (K₂-map-∘ (m₂ ∘2Mσ m₁) σ₃))
        (fst (apK₂ (assoc-wksgrphom (sgrphom-forg m₃) (sgrphom-forg m₂) (sgrphom-forg m₁))))
        (fst (K₂-map-∘ σ₁ (m₃ ∘2Mσ m₂)))
        (fst (K₂-map-∘ σ₂ σ₃))
        (loop G₁ x)
        {δ₁ x} {δ₂ x} {δ₃ x} {δ₄ x} {δ₅ x}
        K₂-β-1 K₂-β-2 K₂-β-3 K₂-β-4 K₂-β-5
