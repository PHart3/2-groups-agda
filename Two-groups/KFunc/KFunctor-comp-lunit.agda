{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import 2Semigroup
open import 2SGrpMap
open import 2Grp
open import K-hom2-ind
open import KFunctor
open import KFunctor-idf
open import KFunctor-comp
open import apK
open import KFunctor-comp-lunit-aux3

module KFunctor-comp-lunit where

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {f : G₁ → G₂} (σ : WkSGrpHomStr f) where

  open KFCLU3 σ

  abstract
    KFunc-lunit :
      apK₂ (unit-wksgrphom-l (sgrphom-forg (cohsgrphom f {{σ}}))) ∙⊙∼
      K₂-map-∘ σ idf2G ∙⊙∼
      ⊙∘-pre (K₂-map⊙ σ) (K₂-map-idf {{η₂}})
        ⊙→∼
      ⊙∘-lunit (K₂-map⊙ σ)
    fst KFunc-lunit = K₂-∼∼-ind idp KFunc-lunit-coher
    snd KFunc-lunit = idp
