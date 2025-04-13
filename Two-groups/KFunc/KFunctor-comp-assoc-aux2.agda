{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import 2Semigroup
open import 2SGrpMap
open import 2Grp
open import Delooping
open import KFunctor
open import KFunctor-comp
open import apK

module KFunctor-comp-assoc-aux2 where

module KFCA2 {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {G₁ : Type ℓ₁} {G₂ : Type ℓ₂} {G₃ : Type ℓ₃} {G₄ : Type ℓ₄}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}} {{η₄ : CohGrp G₄}}
  {f₁ : G₁ → G₂} (σ₁ : WkSGrpHomStr f₁) {f₂ : G₂ → G₃}
  (σ₂ : WkSGrpHomStr f₂) {f₃ : G₃ → G₄} (σ₃ : WkSGrpHomStr f₃) (x : G₁) where

  open import KFunctor-comp-assoc-defs σ₁ σ₂ σ₃
  open import KFunctor-comp-assoc-defs2 σ₁ σ₂ σ₃ x

  abstract
    KFunc-assoc-coher1 : Λ₁ =ₛ Λ₈
    KFunc-assoc-coher1 =
      Λ₁
        =ₛ⟨ 7 & 3 &
          !-=ₛ (ap-seq-=ₛ(λ q → q)
            {s = ∘-ap (K₂-map σ₃) (K₂-map (m₂ ∘2Mσ m₁)) (loop G₁ x) ◃∙
                 idp ◃∙
                 ap-∘ (K₂-map σ₃) (K₂-map (m₂ ∘2Mσ m₁)) (loop G₁ x) ◃∎}
            {t = idp ◃∎}
            (=ₛ-in (∘-ap-ap-∘-inv (K₂-map σ₃) (K₂-map (m₂ ∘2Mσ m₁)) (loop G₁ x)))) ⟩
      _
        =ₛ₁⟨ 8 & 1 &
          ap ! (ap-! (λ q → q) (ap (ap (K₂-map σ₃)) (K₂-map-β-pts (m₂ ∘2Mσ m₁) x)) ∙
               ap ! (ap-idf (ap (ap (K₂-map σ₃)) (K₂-map-β-pts (m₂ ∘2Mσ m₁) x)))) ⟩
      _
        =ₛ₁⟨ 6 & 3 & !-inv-r (! (ap (ap (K₂-map σ₃)) (K₂-map-β-pts (m₂ ∘2Mσ m₁) x))) ⟩
      Λ₂
        =ₛ₁⟨ 8 & 2 & !-inv-l (ap (λ q → q) (K₂-map-β-pts (m₃ ∘2Mσ (m₂ ∘2M m₁)) x)) ⟩
      Λ₃
        =ₛ₁⟨ 8 & 3 & ap-!-inv-l (λ q → q) (K₂-map-β-pts ((m₃ ∘2M m₂) ∘2Mσ m₁) x) ⟩
      Λ₄
        =ₛ⟨ 11 & 2 &
          ap-seq-=ₛ (λ q → q)
            {s = ∘-ap (K₂-map (m₃ ∘2Mσ m₂)) (K₂-map σ₁) (loop G₁ x) ◃∙ ap-∘ (K₂-map (m₃ ∘2Mσ m₂)) (K₂-map σ₁) (loop G₁ x) ◃∎}
            {t = idp ◃∎}
            (=ₛ-in (∘-ap-ap-∘-inv (K₂-map (m₃ ∘2Mσ m₂)) (K₂-map σ₁) (loop G₁ x))) ⟩
      _
        =ₛ⟨ 10 & 3 &
          ap-seq-=ₛ (λ q → q)
          {s =
            ! (ap (ap (K₂-map (m₃ ∘2Mσ m₂))) (K₂-map-β-pts σ₁ x)) ◃∙
            idp ◃∙
            ap (ap (K₂-map (m₃ ∘2Mσ m₂))) (K₂-map-β-pts σ₁ x) ◃∎}
          {t = idp ◃∎}
          (=ₛ-in (!-inv-l (ap (ap (K₂-map (m₃ ∘2Mσ m₂))) (K₂-map-β-pts σ₁ x)))) ⟩
      Λ₅
        =ₛ₁⟨ 8 & 4 & ap-!-inv-l (λ q → q) (K₂-map-β-pts (m₃ ∘2Mσ m₂) (f₁ x)) ⟩
      Λ₆
        =ₛ₁⟨ 6 & 4 & !-inv-l (ap (λ q → q) (! (K₂-map-β-pts σ₃ (f₂ (f₁ x))))) ⟩
      Λ₇
        =ₛ₁⟨ 7 & 1 & ap-idf (! (ap (ap (K₂-map σ₃)) (K₂-map-β-pts σ₂ (f₁ x)))) ⟩
      _
        =ₛ⟨ 5 & 3 &
          !-=ₛ
            (=ₛ-in
              {s = ap (ap (K₂-map σ₃)) (K₂-map-β-pts σ₂ (f₁ x)) ◃∙ idp ◃∙ ap (ap (K₂-map σ₃)) (! (K₂-map-β-pts σ₂ (f₁ x))) ◃∎}
              {t = idp ◃∎}
              (ap-!-inv (ap (K₂-map σ₃)) (K₂-map-β-pts σ₂ (f₁ x)))) ⟩
      Λ₈ ∎ₛ
