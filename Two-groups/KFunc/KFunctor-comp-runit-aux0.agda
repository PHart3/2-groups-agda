{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import 2Magma
open import 2MagMap
open import 2Grp
open import Delooping
open import K-hom-ind
open import KFunctor
open import KFunctor-idf
open import KFunctor-comp
open import apK

module KFunctor-comp-runit-aux0 where

module KFCRU0 {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  {f : G₁ → G₂} (σ : WkMagHomStr f) (x : G₁) where

  private
    ν₁ =
      λ v →
        K₂-map-β-pts σ v ∙
        (! (K₂-map-β-pts (cohmaghom f {{σ}} ∘2Mσ cohmaghom (λ z → z) {{idf2G}}) v) :> (loop G₂ (f v) == ap (K₂-map (cohmaghom f {{σ}} ∘2Mσ cohmaghom (λ z → z) {{idf2G}})) (loop G₁ v)))
    ν₂-suff =
      λ v →
        ! (K₂-map-β-pts σ v) ∙
        (! (ap (ap (K₂-map σ)) (K₂-map-β-pts idf2G v)) :> (ap (K₂-map σ) (loop G₁ v) == ap (K₂-map σ) (ap (K₂-map idf2G) (loop G₁ v)))) ∙
        ∘-ap (K₂-map σ) (K₂-map idf2G) (loop G₁ v)
    ν₂ =
      λ v →
        K₂-map-β-pts (cohmaghom f {{σ}} ∘2Mσ cohmaghom (λ z → z) {{idf2G}}) v ∙
        (ν₂-suff v :> (loop G₂ (f v) == ap (K₂-map σ ∘ K₂-map idf2G) (loop G₁ v)))
    ν₃ = λ v → K₂-map-β-pts idf2G v ∙ ! (ap-idf (loop G₁ v))

  abstract

    K₂-β-1 :
      hmtpy-nat-∙' (fst (apK₂ (unit-wkmaghom-r (maghom-forg (cohmaghom f {{σ}}))))) (loop G₁ x) ◃∎
        =ₛ
      K₂-map-β-pts σ x ◃∙
      ! (K₂-map-β-pts (cohmaghom f {{σ}} ∘2Mσ cohmaghom (λ z → z) {{idf2G}}) x) ◃∎
    K₂-β-1 = =ₛ-in $
      K₂-∼-ind-β (K₂-map σ) (K₂-map (cohmaghom f {{σ}} ∘2Mσ cohmaghom (λ z → z) {{idf2G}}))
        (idp :> (base G₂ == base G₂))
        ν₁
        _ x

    K₂-β-2 :
      hmtpy-nat-∙' (fst (K₂-map-∘ idf2G σ)) (loop G₁ x) ◃∎
        =ₛ
      K₂-map-β-pts (cohmaghom f {{σ}} ∘2Mσ cohmaghom (λ z → z) {{idf2G}}) x ◃∙
      ! (K₂-map-β-pts σ x) ◃∙
      ! (ap (ap (K₂-map σ)) (K₂-map-β-pts idf2G x)) ◃∙
      ∘-ap (K₂-map σ) (K₂-map idf2G) (loop G₁ x) ◃∎
    K₂-β-2 = =ₛ-in $
      K₂-∼-ind-β
        (map₁-∘ idf2G σ)
        (map₂-∘ idf2G σ)
        (idp :> (base G₂ == base G₂))
        ν₂
        _ x

    K₂-β-3 :
      hmtpy-nat-∙' (fst (K₂-map-idf {{η₁}})) (loop G₁ x) ◃∎
        =ₛ
      K₂-map-β-pts idf2G x ◃∙
      ! (ap-idf (loop G₁ x)) ◃∎
    K₂-β-3 = =ₛ-in $
      K₂-∼-ind-β
        (K₂-map idf2G)
        (idf (K₂ G₁ η₁))
        idp
        ν₃
        _ x
