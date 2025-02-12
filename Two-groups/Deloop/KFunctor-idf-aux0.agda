{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp
open import Delooping
open import KFunctor

module KFunctor-idf-aux0 where

open CohGrp {{...}}

module _ {i} {G : Type i} {{η : CohGrp G}} where

  module _ (x y : G) where

    K₂-map-idf-coher0 = 
      ∙-ap (K₂-map idf2G) (loop G x) (loop G y) ◃∙
      ap (ap (K₂-map idf2G)) (loop-comp G x y) ◃∙
      (K₂-map-β-pts idf2G (mu x y) ∙
      ! (ap-idf (loop G (mu x y))) ∙
      ! (∙-unit-r (ap (idf (K₂ G η)) (loop G (mu x y))))) ◃∎
        =ₑ⟨ 2 & 1 &
          (K₂-map-β-pts idf2G (mu x y) ◃∙
          ! (ap-idf (loop G (mu x y))) ◃∙
          ! (∙-unit-r (ap (idf (K₂ G η)) (loop G (mu x y)))) ◃∎)
        % =ₛ-in idp ⟩
      ∙-ap (K₂-map idf2G) (loop G x) (loop G y) ◃∙
      ap (ap (K₂-map idf2G)) (loop-comp G x y) ◃∙
      K₂-map-β-pts idf2G (mu x y) ◃∙
      ! (ap-idf (loop G (mu x y))) ◃∙
      ! (∙-unit-r (ap (idf (K₂ G η)) (loop G (mu x y)))) ◃∎
        =ₛ⟨ 2 & 1 & K₂-map-β-comp idf2G x y ⟩
      ∙-ap (K₂-map idf2G) (loop G x) (loop G y) ◃∙
      ap (ap (K₂-map idf2G)) (loop-comp G x y) ◃∙
      ! (ap (ap (K₂-map idf2G)) (loop-comp G x y)) ◃∙
      ! (∙-ap (K₂-map idf2G) (loop G x) (loop G y)) ◃∙
      ap2 _∙_ (K₂-map-β-pts idf2G x) (K₂-map-β-pts idf2G y) ◃∙
      loop-comp G x y ◃∙
      idp ◃∙
      ! (ap-idf (loop G (mu x y))) ◃∙
      ! (∙-unit-r (ap (idf (K₂ G η)) (loop G (mu x y)))) ◃∎
        =ₛ₁⟨ 1 & 2 & !-inv-r (ap (ap (K₂-map idf2G)) (loop-comp G x y)) ⟩
      ∙-ap (K₂-map idf2G) (loop G x) (loop G y) ◃∙
      idp ◃∙
      ! (∙-ap (K₂-map idf2G) (loop G x) (loop G y)) ◃∙
      ap2 _∙_ (K₂-map-β-pts idf2G x) (K₂-map-β-pts idf2G y) ◃∙
      loop-comp G x y ◃∙
      idp ◃∙
      ! (ap-idf (loop G (mu x y))) ◃∙
      ! (∙-unit-r (ap (idf (K₂ G η)) (loop G (mu x y)))) ◃∎ ∎ₛ
