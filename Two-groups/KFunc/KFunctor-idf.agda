{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp
open import Delooping
open import K-hom-ind
open import KFunctor
open import KFunctor-idf-aux0
open import KFunctor-idf-aux1
open import KFunctor-idf-aux2

-- K₂-map respects identity

module KFunctor-idf where

open CohGrp {{...}}

module _ {i} {G : Type i} {{η : CohGrp G}} where

  abstract
    K₂-map-idf-coher : (x y : G) →    
      ∙-ap (K₂-map idf2G) (loop G x) (loop G y) ◃∙
      ap (ap (K₂-map idf2G)) (loop-comp G x y) ◃∙
      (K₂-map-β-pts idf2G (mu x y) ∙
      ! (ap-idf (loop G (mu x y)))) ◃∎
        =ₛ
      ap2 _∙_
        (K₂-map-β-pts idf2G x ∙ ! (ap-idf (loop G x)))
        (K₂-map-β-pts idf2G y ∙ ! (ap-idf (loop G y))) ◃∙
      ∙-assoc2-!-inv-l (idf (K₂ G η)) idp idp (loop G x) (loop G y) ◃∙
      ap (λ p → ap (idf (K₂ G η)) p) (loop-comp G x y) ◃∎
    K₂-map-idf-coher x y = K₂-map-idf-coher0 x y ∙ₛ K₂-map-idf-coher1 x y ∙ₛ K₂-map-idf-coher2 x y

  K₂-map-idf : K₂-map⊙ idf2G ⊙-comp (idf (K₂ G η) , idp)
  fst K₂-map-idf =
    K₂-∼-ind (K₂-map idf2G) (idf (K₂ G η))
      idp
      (λ x → K₂-map-β-pts idf2G x ∙ ! (ap-idf (loop G x)))
      K₂-map-idf-coher
  snd K₂-map-idf = idp
