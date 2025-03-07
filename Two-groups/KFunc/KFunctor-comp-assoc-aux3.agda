{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import 2Magma
open import 2MagMap
open import 2Grp
open import Delooping
open import KFunctor
open import KFunctor-comp
open import apK
open import KFunctor-comp-assoc-aux1
open import KFunctor-comp-assoc-aux2

module KFunctor-comp-assoc-aux3 where

module KFCA3 {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {G₁ : Type ℓ₁} {G₂ : Type ℓ₂} {G₃ : Type ℓ₃} {G₄ : Type ℓ₄}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}} {{η₄ : CohGrp G₄}}
  {f₁ : G₁ → G₂} (σ₁ : WkMagHomStr f₁) {f₂ : G₂ → G₃}
  (σ₂ : WkMagHomStr f₂) {f₃ : G₃ → G₄} (σ₃ : WkMagHomStr f₃) (x : G₁) where

  open import KFunctor-comp-assoc-defs σ₁ σ₂ σ₃
  open import KFunctor-comp-assoc-defs2 σ₁ σ₂ σ₃ x

  open KFCA1 σ₁ σ₂ σ₃ x
  open KFCA2 σ₁ σ₂ σ₃ x

  abstract
    KFunc-assoc-coher2 : Λ₈ =ₛ hmtpy-nat-∙' (λ z → idp) (loop G₁ x) ◃∎
    KFunc-assoc-coher2 =
      Λ₈
        =ₛ₁⟨ 4 & 4 & lemma1 (K₂-map-β-pts σ₁ x) ⟩
      Λ₉
        =ₛ₁⟨ lemma2 (loop G₁ x) ⟩
      hmtpy-nat-∙' (λ z → idp) (loop G₁ x) ◃∎ ∎ₛ
        where
          lemma1 : {t₁ t₂ : base G₂ == base G₂} (p : t₁ == t₂) →
            ! (ap (ap (K₂-map σ₃)) (! (ap (ap (K₂-map σ₂)) p))) ∙
            ap (λ q → q) (∘-ap (K₂-map σ₃) (K₂-map σ₂) t₂) ∙
            ap (λ q → q) (! (ap (ap (K₂-map σ₃ ∘ K₂-map σ₂)) p))
              ==
            ∘-ap (K₂-map σ₃) (K₂-map σ₂) t₁
          lemma1 {t₁} idp = ∙-unit-r (ap (λ q → q) (∘-ap (K₂-map σ₃) (K₂-map σ₂) t₁)) ∙ ap-idf (∘-ap (K₂-map σ₃) (K₂-map σ₂) t₁)

          lemma2 : {b : K₂ G₁ η₁} (p : base G₁ == b) →
            ! (ap (λ q → q) (ap (λ q → q) (∘-ap (K₂-map σ₃) (K₂-map σ₂ ∘ K₂-map σ₁) p))) ∙
            ! (ap (ap (K₂-map σ₃)) (∘-ap (K₂-map σ₂) (K₂-map σ₁) p)) ∙
            ∘-ap (K₂-map σ₃) (K₂-map σ₂) (ap (K₂-map σ₁) p) ∙
            ap (λ q → q) (ap (λ q → q) (∘-ap (K₂-map σ₃ ∘ K₂-map σ₂) (K₂-map σ₁) p)) ∙ idp
              ==
            hmtpy-nat-∙' (λ z → idp) p
          lemma2 idp = idp

  abstract
    KFunc-assoc-coher :
      hmtpy-nat-∙'
        (λ z →
           ! (ap (K₂-map σ₃) (fst (K₂-map-∘ σ₁ σ₂) z)) ∙
           ! (fst (K₂-map-∘ (m₂ ∘2Mσ m₁) σ₃) z) ∙
           fst (apK₂ (assoc-wkmaghom (maghom-forg m₃) (maghom-forg m₂) (maghom-forg m₁))) z ∙
           fst (K₂-map-∘ σ₁ (m₃ ∘2Mσ m₂)) z ∙
           fst (K₂-map-∘ σ₂ σ₃) (K₂-map σ₁ z))
        (loop G₁ x) ◃∎
        =ₛ
      hmtpy-nat-∙' (λ z → idp) (loop G₁ x) ◃∎
    KFunc-assoc-coher = KFunc-assoc-coher0 ∙ₛ (KFunc-assoc-coher1 ∙ₛ KFunctor-assoc-coher2)


  abstract
    KFunc-assoc-coher-out :
      hmtpy-nat-∙'
        (λ z →
           ! (ap (K₂-map σ₃) (fst (K₂-map-∘ σ₁ σ₂) z)) ∙
           ! (fst (K₂-map-∘ (m₂ ∘2Mσ m₁) σ₃) z) ∙
           fst (apK₂ (assoc-wkmaghom (maghom-forg m₃) (maghom-forg m₂) (maghom-forg m₁))) z ∙
           fst (K₂-map-∘ σ₁ (m₃ ∘2Mσ m₂)) z ∙
           fst (K₂-map-∘ σ₂ σ₃) (K₂-map σ₁ z))
        (loop G₁ x)
        ==
      hmtpy-nat-∙' (λ z → idp) (loop G₁ x)
    KFunc-assoc-coher-out = =ₛ-out KFunc-assoc-coher
