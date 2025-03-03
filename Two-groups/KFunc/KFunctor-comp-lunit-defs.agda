{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import lib.Basics
open import 2Magma
open import 2Grp
open import Delooping
open import KFunctor

module KFunctor-comp-lunit-defs
  {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  {f : G₁ → G₂} (σ : WkMagHomStr f) (x : G₁) where

  Λ₁ = 
    K₂-map-β-pts σ x ◃∙
    ! (K₂-map-β-pts (cohmaghom f {{σ}} ∘2Mσ cohmaghom (λ z → z) {{idf2G}}) x) ◃∙
    ap (λ q → q) (K₂-map-β-pts (cohgrphom f {{σ}} ∘2Gσ cohgrphom (idf G₁) {{idf2G}}) x) ◃∙
    ap (λ q → q) (! (K₂-map-β-pts σ x)) ◃∙
    ap (λ q → q) (! (ap (ap (K₂-map σ)) (K₂-map-β-pts idf2G x))) ◃∙
    ap (λ q → q) (∘-ap (K₂-map σ) (K₂-map idf2G) (loop G₁ x)) ◃∙
    ap (λ q → q) (ap-∘ (K₂-map σ) (K₂-map idf2G) (loop G₁ x)) ◃∙
    ap (ap (K₂-map σ)) (K₂-map-β-pts idf2G x) ◃∙
    ap (ap (K₂-map σ)) (! (ap-idf (loop G₁ x))) ◃∙
    idp ◃∙
    ap (λ q → q) (ap (λ q → q) (∘-ap (K₂-map σ) (λ z → z) (loop G₁ x))) ◃∙
    idp ◃∙
    idp ◃∎
