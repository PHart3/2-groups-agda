{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import 2Magma
open import 2MagMap
open import 2Grp
open import Delooping
open import KFunctor
open import KFunctor-comp
open import apK

module KFunctor-comp-assoc-aux2 where

module KFCA2 {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {G₁ : Type ℓ₁} {G₂ : Type ℓ₂} {G₃ : Type ℓ₃} {G₄ : Type ℓ₄}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}} {{η₄ : CohGrp G₄}}
  {f₁ : G₁ → G₂} (σ₁ : WkMagHomStr f₁) {f₂ : G₂ → G₃}
  (σ₂ : WkMagHomStr f₂) {f₃ : G₃ → G₄} (σ₃ : WkMagHomStr f₃) (x : G₁) where

  open import KFunctor-comp-assoc-defs σ₁ σ₂ σ₃
  open import KFunctor-comp-assoc-defs2 σ₁ σ₂ σ₃ x

  abstract
    KFunc-assoc-coher1 : Λ₁ =ₛ Λ₈
    KFunc-assoc-coher1 =
      Λ₁
        =ₛ₁⟨ 8 & 4 & {!!} ⟩
      {!!}
