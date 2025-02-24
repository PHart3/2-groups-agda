{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp
open import Delooping
open import KFunctor

module KFunctor-idf-aux1 where

open CohGrp {{...}}

module _ {i} {G : Type i} {{η : CohGrp G}} where

  module _ (x y : G) where
     
    K₂-map-idf-coher1 =
      ∙-ap (K₂-map idf2G) (loop G x) (loop G y) ◃∙
      idp ◃∙
      ! (∙-ap (K₂-map idf2G) (loop G x) (loop G y)) ◃∙
      ap2 _∙_ (K₂-map-β-pts idf2G x) (K₂-map-β-pts idf2G y) ◃∙
      loop-comp G x y ◃∙
      idp ◃∙
      ! (ap-idf (loop G (mu x y))) ◃∎
        =ₛ₁⟨ 0 & 3 & !-inv-r (∙-ap (K₂-map idf2G) (loop G x) (loop G y)) ⟩
      idp ◃∙
      ap2 _∙_ (K₂-map-β-pts idf2G x) (K₂-map-β-pts idf2G y) ◃∙
      loop-comp G x y ◃∙
      idp ◃∙
      ! (ap-idf (loop G (mu x y))) ◃∎
        =ₛ₁⟨ 3 & 3 &  =ₛ-out (apCommSq2◃ (λ p → ! (ap-idf p)) (loop-comp G x y)) ⟩
      idp ◃∙
      ap2 _∙_ (K₂-map-β-pts idf2G x) (K₂-map-β-pts idf2G y) ◃∙
      loop-comp G x y ◃∙
      (! (ap (λ z → z) (loop-comp G x y)) ∙
      ! (ap-idf (loop G x ∙ loop G y)) ∙
      ap (ap (idf (K₂ G η))) (loop-comp G x y)) ◃∎
        =ₑ⟨ 3 & 1 &
            (! (ap (λ z → z) (loop-comp G x y)) ◃∙
            ! (ap-idf (loop G x ∙ loop G y)) ◃∙
            ap (λ z → ap (idf (K₂ G η)) z) (loop-comp G x y) ◃∎)
          % =ₛ-in idp ⟩
      idp ◃∙
      ap2 _∙_ (K₂-map-β-pts idf2G x) (K₂-map-β-pts idf2G y) ◃∙
      loop-comp G x y ◃∙
      ! (ap (λ z → z) (loop-comp G x y)) ◃∙
      ! (ap-idf (loop G x ∙ loop G y)) ◃∙
      ap (ap (idf (K₂ G η))) (loop-comp G x y) ◃∎
        =ₛ₁⟨ 2 & 2 & ap (λ p → loop-comp G x y ∙ ! p) (ap-idf (loop-comp G x y)) ∙ !-inv-r (loop-comp G x y) ⟩
      idp ◃∙
      ap2 _∙_ (K₂-map-β-pts idf2G x) (K₂-map-β-pts idf2G y) ◃∙
      idp ◃∙
      ! (ap-idf (loop G x ∙ loop G y)) ◃∙
      ap (ap (idf (K₂ G η))) (loop-comp G x y) ◃∎ ∎ₛ
