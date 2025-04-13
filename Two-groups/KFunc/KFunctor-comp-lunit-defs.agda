{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import lib.Basics
open import 2Semigroup
open import 2Grp
open import Delooping
open import KFunctor

module KFunctor-comp-lunit-defs
  {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  {f : G₁ → G₂} (σ : WkSGrpHomStr f) (x : G₁) where

  Λ₁ =
    K₂-map-β-pts σ x ◃∙
    ! (K₂-map-β-pts (cohsgrphom (λ z → z) {{idf2G}} ∘2Mσ cohsgrphom f {{σ}}) x) ◃∙
    ap (λ q → q) (K₂-map-β-pts (cohgrphom (idf G₂) {{idf2G}} ∘2Gσ cohgrphom f {{σ}}) x) ◃∙
    ap (λ q → q) (! (K₂-map-β-pts idf2G (f x))) ◃∙
    ap (λ q → q) (! (ap (ap (K₂-map idf2G)) (K₂-map-β-pts σ x))) ◃∙
    ap (λ q → q) (∘-ap (K₂-map idf2G) (K₂-map σ) (loop G₁ x)) ◃∙
    ap (λ q → q) (ap-∘ (K₂-map idf2G) (K₂-map σ) (loop G₁ x)) ◃∙
    ap (λ q → q) (ap (ap (K₂-map idf2G)) (K₂-map-β-pts σ x)) ◃∙
    ap (λ q → q) (K₂-map-β-pts idf2G (f x)) ◃∙
    ap (λ q → q) (! (ap-idf (loop G₂ (f x)))) ◃∙
    ap (λ q → q) (! (ap (ap (idf (K₂ G₂ η₂))) (K₂-map-β-pts σ x))) ◃∙
    ap (λ q → q) (ap (λ q → q) (∘-ap (λ z → z) (K₂-map σ) (loop G₁ x))) ◃∙
    idp ◃∙
    idp ◃∎

  Λ₂ =
    K₂-map-β-pts σ x ◃∙
    ! (K₂-map-β-pts (cohsgrphom (λ z → z) {{idf2G}} ∘2Mσ cohsgrphom f {{σ}}) x) ◃∙
    ap (λ q → q) (K₂-map-β-pts (cohgrphom (idf G₂) {{idf2G}} ∘2Gσ cohgrphom f {{σ}}) x) ◃∙
    ap (λ q → q) (! (K₂-map-β-pts idf2G (f x))) ◃∙
    idp ◃∙
    ap (λ q → q) (K₂-map-β-pts idf2G (f x)) ◃∙
    ap (λ q → q) (! (ap-idf (loop G₂ (f x)))) ◃∙
    ap (λ q → q) (! (ap (ap (idf (K₂ G₂ η₂))) (K₂-map-β-pts σ x))) ◃∙
    ap (λ q → q) (ap (λ q → q) (∘-ap (λ z → z) (K₂-map σ) (loop G₁ x))) ◃∙
    idp ◃∙
    idp ◃∎

  Λ₃ =
    K₂-map-β-pts σ x ◃∙
    idp ◃∙
    ap (λ q → q) (! (K₂-map-β-pts idf2G (f x))) ◃∙
    idp ◃∙
    ap (λ q → q) (K₂-map-β-pts idf2G (f x)) ◃∙
    ap (λ q → q) (! (ap-idf (loop G₂ (f x)))) ◃∙
    ap (λ q → q) (! (ap (ap (idf (K₂ G₂ η₂))) (K₂-map-β-pts σ x))) ◃∙
    ap (λ q → q) (ap (λ q → q) (∘-ap (λ z → z) (K₂-map σ) (loop G₁ x))) ◃∙
    idp ◃∙
    idp ◃∎

  Λ₄ =
    K₂-map-β-pts σ x ◃∙
    idp ◃∙
    idp ◃∙
    ap (λ q → q) (! (ap-idf (loop G₂ (f x)))) ◃∙
    ap (λ q → q) (! (ap (ap (idf (K₂ G₂ η₂))) (K₂-map-β-pts σ x))) ◃∙
    ap (λ q → q) (ap (λ q → q) (∘-ap (λ z → z) (K₂-map σ) (loop G₁ x))) ◃∙
    idp ◃∙
    idp ◃∎
