{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import 2Semigroup
open import 2SGrpMap
open import 2Grp
open import Delooping
open import KFunctor
open import KFunctor-idf
open import KFunctor-comp
open import apK
open import KFunctor-comp-runit-aux1
open import KFunctor-comp-runit-aux2

module KFunctor-comp-runit-aux3 where

module KFCRU3 {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  {f : G₁ → G₂} (σ : WkSGrpHomStr f) (x : G₁) where

  open KFCRU1 σ x
  open KFCRU2 σ x

  abstract
    KFunc-runit-coher :
      hmtpy-nat-∙'
        (λ z →
          fst (apK₂ (unit-wksgrphom-r (sgrphom-forg (cohsgrphom f {{σ}})))) z ∙
          fst (K₂-map-∘ idf2G σ) z ∙
          ap (K₂-map σ) (fst (K₂-map-idf {{η₁}}) z))
        (loop G₁ x)
        ==
      hmtpy-nat-∙' (λ z → idp) (loop G₁ x)
    KFunc-runit-coher = =ₛ-out $
      KFunc-runit-coher0 ∙ₛ (KFunc-runit-coher1 ∙ₛ (KFunc-runit-coher2 ∙ₛ KFunc-runit-coher3 (loop G₁ x)))
