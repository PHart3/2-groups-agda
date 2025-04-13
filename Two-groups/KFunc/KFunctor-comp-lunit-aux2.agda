{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import lib.Basics
open import 2Semigroup
open import 2SGrpMap
open import 2Grp
open import Delooping
open import KFunctor

module KFunctor-comp-lunit-aux2 where

module KFCLU2 {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  {f : G₁ → G₂} (σ : WkSGrpHomStr f) (x : G₁) where

  open import KFunctor-comp-lunit-defs σ x

  abstract
    KFunc-lunit-coher2-aux : {v : base G₂ == base G₂} (p : v == loop G₂ (f x)) →
      p ∙
      ap (λ q → q) (! (ap-idf (loop G₂ (f x)))) ∙
      ap (λ q → q) (! (ap (ap (idf (K₂ G₂ η₂))) p))
        ==
      ! (ap-idf v)
    KFunc-lunit-coher2-aux idp = ∙-unit-r (ap (λ q → q) (! (ap-idf (loop G₂ (f x))))) ∙ ap-idf (! (ap-idf (loop G₂ (f x))))

  abstract
    KFunc-lunit-coher1 : Λ₁ =ₛ Λ₄
    KFunc-lunit-coher1 =
      Λ₁
        =ₑ⟨ 5 & 2 & idp ◃∎ % ap-seq-=ₛ (λ q → q) (=ₛ-in (∘-ap-ap-∘-inv (K₂-map idf2G) (K₂-map σ) (loop G₁ x))) ⟩
      _
        =ₑ⟨ 4 & 3 & idp ◃∎ % ap-seq-=ₛ (λ q → q) (=ₛ-in (!-inv-l (ap (ap (K₂-map idf2G)) (K₂-map-β-pts σ x)))) ⟩
      Λ₂
        =ₛ₁⟨ 1 & 2 & 
          ap2 _∙_ idp (ap-idf (K₂-map-β-pts (cohsgrphom (idf G₂) {{idf2G}} ∘2Mσ cohsgrphom f {{σ}}) x)) ∙
          !-inv-l (K₂-map-β-pts (cohsgrphom (idf G₂) {{idf2G}} ∘2Mσ cohsgrphom f {{σ}}) x) ⟩
      Λ₃
        =ₑ⟨ 2 & 3 & idp ◃∎ % ap-seq-=ₛ (λ q → q) (=ₛ-in (!-inv-l (K₂-map-β-pts idf2G (f x)))) ⟩
      Λ₄ ∎ₛ

    KFunc-lunit-coher2 : Λ₄ =ₛ hmtpy-nat-∙' (λ x₁ → idp) (loop G₁ x) ◃∎
    KFunc-lunit-coher2 =
      Λ₄
        =ₛ₁⟨ 0 & 5 & KFunc-lunit-coher2-aux (K₂-map-β-pts σ x) ⟩
      ! (ap-idf (ap (K₂-map σ) (loop G₁ x))) ◃∙
      ap (λ q → q) (ap (λ q → q) (∘-ap (λ z → z) (K₂-map σ) (loop G₁ x))) ◃∙
      idp ◃∙
      idp ◃∎
        =ₛ₁⟨ lemma (loop G₁ x) ⟩
      hmtpy-nat-∙' (λ x₁ → idp) (loop G₁ x) ◃∎ ∎ₛ
        where
          lemma : {b : K₂ G₁ η₁} (p : b == base G₁) →
            ! (ap-idf (ap (K₂-map σ) p)) ∙
            ap (λ q → q) (ap (λ q → q) (∘-ap (λ z → z) (K₂-map σ) p)) ∙ idp
              ==
            hmtpy-nat-∙' (λ x₁ → idp) p
          lemma idp = idp
