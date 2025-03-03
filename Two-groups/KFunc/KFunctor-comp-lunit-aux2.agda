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

module KFunctor-comp-lunit-aux2 where

module KFCLU2 {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  {f : G₁ → G₂} (σ : WkMagHomStr f) (x : G₁) where

  open import KFunctor-comp-lunit-defs σ x

  -- GOAL : Λ₁ =ₛ hmtpy-nat-∙' (λ x₁ → idp) (loop G₁ x) ◃∎

  abstract
    KFunc-runit-coher1 :
      Λ₁
        =ₛ
      ?
    KFunc-runit-coher1 = ?
