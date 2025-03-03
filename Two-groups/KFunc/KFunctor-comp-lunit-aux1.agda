{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import lib.PathFunctor6
open import 2Magma
open import 2MagMap
open import 2Grp
open import Delooping
open import KFunctor
open import KFunctor-idf
open import KFunctor-comp
open import apK
open import KFunctor-comp-lunit-aux0

module KFunctor-comp-lunit-aux1 where

module KFCLU1 {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  {f : G₁ → G₂} (σ : WkMagHomStr f) (x : G₁) where

  open KFCLU0 σ x
  
  open import KFunctor-comp-lunit-defs σ x

  abstract
    KFunc-lunit-coher0 :
      hmtpy-nat-∙'
        (λ z →
          fst (apK₂ (unit-wkmaghom-l (maghom-forg (cohmaghom f {{σ}})))) z ∙
          fst (K₂-map-∘ σ idf2G) z ∙
          fst (K₂-map-idf {{η₂}}) (K₂-map σ z))
        (loop G₁ x) ◃∎
        =ₛ
      Λ₁
    KFunc-lunit-coher0 = 
      hnat-∙'-∙-pre (K₂-map σ)
        (fst (apK₂ (unit-wkmaghom-l (maghom-forg (cohmaghom f {{σ}})))))
        (fst (K₂-map-∘ σ idf2G))
        (fst (K₂-map-idf {{η₂}}))
        (loop G₁ x)
        K₂-β-1 K₂-β-2 K₂-β-3
