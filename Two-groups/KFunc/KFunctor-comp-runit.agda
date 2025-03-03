{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import 2Magma
open import 2MagMap
open import 2Grp
open import K-hom2-ind
open import KFunctor
open import KFunctor-idf
open import KFunctor-comp
open import apK
open import KFunctor-comp-lunit-aux3

module KFunctor-comp-lunit where

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {f : G₁ → G₂} (σ : WkMagHomStr f) where

  open KFCLU3 σ

  abstract
    KFunc-runit :
      apK₂ (unit-wkmaghom-r (maghom-forg (cohmaghom f {{σ}}))) ∙⊙∼
      K₂-map-∘ idf2G σ ∙⊙∼
      ⊙∘-post (K₂-map⊙ σ) (K₂-map-idf {{η₁}})
        ⊙→∼
      ⊙∘-runit (K₂-map⊙ σ)
    fst KFunc-runit = K₂-∼∼-ind idp KFunc-runit-coher
    snd KFunc-runit = =ₛ-in idp
