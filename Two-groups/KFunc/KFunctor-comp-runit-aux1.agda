{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import lib.PathFunctor6
open import 2Semigroup
open import 2SGrpMap
open import 2Grp
open import Delooping
open import KFunctor
open import KFunctor-idf
open import KFunctor-comp
open import apK
open import KFunctor-comp-runit-aux0

module KFunctor-comp-runit-aux1 where

module KFCRU1 {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  {f : G₁ → G₂} (σ : WkSGrpHomStr f) (x : G₁) where

  open KFCRU0 σ x

  open import KFunctor-comp-runit-defs σ x

  abstract
    KFunc-runit-coher0 :
      hmtpy-nat-∙'
        (λ z →
          fst (apK₂ (unit-wksgrphom-r (sgrphom-forg (cohsgrphom f {{σ}})))) z ∙
          fst (K₂-map-∘ idf2G σ) z ∙
          ap (K₂-map σ) (fst (K₂-map-idf {{η₁}}) z))
        (loop G₁ x) ◃∎
        =ₛ
      Λ₁
    KFunc-runit-coher0 = 
      hnat-∙'-∙-post (K₂-map σ)
        (fst (apK₂ (unit-wksgrphom-r (sgrphom-forg (cohsgrphom f {{σ}})))))
        (fst (K₂-map-∘ idf2G σ))
        (fst (K₂-map-idf {{η₁}}))
        (loop G₁ x)
        K₂-β-1 K₂-β-2 K₂-β-3
