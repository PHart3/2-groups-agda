{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import 2Magma
open import 2MagMap
open import 2Grp
open import Delooping
open import KFunctor
open import KFunctor-idf
open import KFunctor-comp
open import apK
open import KFunctor-comp-lunit-aux1
open import KFunctor-comp-lunit-aux2

module KFunctor-comp-lunit-aux3 where

module KFCLU3 {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  {f : G₁ → G₂} (σ : WkMagHomStr f) (x : G₁) where

  open KFCLU1 σ x
  open KFCLU2 σ x

  abstract
    KFunc-lunit-coher :
      hmtpy-nat-∙'
        (λ z →
          fst (apK₂ (unit-wkmaghom-l (maghom-forg (cohmaghom f {{σ}})))) z ∙
          fst (K₂-map-∘ σ idf2G) z ∙
          fst (K₂-map-idf {{η₂}}) (K₂-map σ z))
        (loop G₁ x)
        ==
      hmtpy-nat-∙' (λ x₁ → idp) (loop G₁ x)
    KFunc-lunit-coher = =ₛ-out (KFunc-lunit-coher0 ∙ₛ (KFunc-lunit-coher1 ∙ₛ KFunc-lunit-coher2))
