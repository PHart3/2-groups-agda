{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp
open import Delooping
open import K-hom-ind
open import KFunctor
open import KFunctor-idf-aux0
open import KFunctor-idf-aux1

-- K₂-map respects identity

module KFunctor-idf where

open CohGrp {{...}}

module _ {i} {G : Type i} {{η : CohGrp G}} where

  module _ (x y : G) where
  
    K₂-map-idf-coher2 =
      idp ◃∙
      ap2 _∙_ (K₂-map-β-pts idf2G x) (K₂-map-β-pts idf2G y) ◃∙
      idp ◃∙
      (! (ap-idf (loop G x ∙ loop G y)) ∙
      ! (∙-unit-r (ap (idf (K₂ G η)) (loop G x ∙ loop G y)))) ◃∙
      ap (λ p → ap (idf (K₂ G η)) p ∙ idp) (loop-comp G x y) ◃∎
        =ₑ⟨ 0 & 4 &
          (ap2 _∙_
            (K₂-map-β-pts idf2G x ∙ ! (ap-idf (loop G x)) ∙ ! (∙-unit-r (ap (idf (K₂ G η)) (loop G x))))
            (K₂-map-β-pts idf2G y ∙ ! (ap-idf (loop G y)) ∙ ! (∙-unit-r (ap (idf (K₂ G η)) (loop G y)))) ◃∙
          ∙-assoc2-!-inv-l (idf (K₂ G η)) idp idp (loop G x) (loop G y) ◃∎)
          % =ₛ-in (lemma (K₂-map-β-pts idf2G x) (K₂-map-β-pts idf2G y)) ⟩
      ap2 _∙_
        (K₂-map-β-pts idf2G x ∙ ! (ap-idf (loop G x)) ∙ ! (∙-unit-r (ap (idf (K₂ G η)) (loop G x))))
        (K₂-map-β-pts idf2G y ∙ ! (ap-idf (loop G y)) ∙ ! (∙-unit-r (ap (idf (K₂ G η)) (loop G y)))) ◃∙
      ∙-assoc2-!-inv-l (idf (K₂ G η)) idp idp (loop G x) (loop G y) ◃∙
      ap (λ p → ap (idf (K₂ G η)) p ∙ idp) (loop-comp G x y) ◃∎ ∎ₛ
        where
          lemma : {p₃ p₄ : base G == base G}
            (p₁ : ap (K₂-map idf2G) (loop G x) == p₃)
            (p₂ : ap (K₂-map idf2G) (loop G y) == p₄) →
            ap2 _∙_ p₁ p₂ ∙
            (! (ap-idf (p₃ ∙ p₄)) ∙
            ! (∙-unit-r (ap (idf (K₂ G η)) (p₃ ∙ p₄))))
              ==
            ap2 _∙_
              (p₁ ∙ ! (ap-idf p₃) ∙ ! (∙-unit-r (ap (idf (K₂ G η)) p₃)))
              (p₂ ∙ ! (ap-idf p₄) ∙ ! (∙-unit-r (ap (idf (K₂ G η)) p₄))) ∙
            ∙-assoc2-!-inv-l (idf (K₂ G η)) idp idp p₃ p₄
          lemma idp idp = aux (ap (K₂-map idf2G) (loop G x)) (ap (K₂-map idf2G) (loop G y))
            where
              aux : {b : K₂ G η} (q₁ : base G == b) (q₂ : b == base G) →
                ! (ap-idf (q₁ ∙ q₂)) ∙
                ! (∙-unit-r (ap (idf (K₂ G η)) (q₁ ∙ q₂)))
                  ==
                ap2 _∙_
                  (! (ap-idf q₁) ∙ ! (∙-unit-r (ap (idf (K₂ G η)) q₁)))
                  (! (ap-idf q₂) ∙ ! (∙-unit-r (ap (idf (K₂ G η)) q₂))) ∙
                ∙-assoc2-!-inv-l (idf (K₂ G η)) idp idp q₁ q₂
              aux idp q₂ = aux2 q₂
                where
                  aux2 : {b : K₂ G η} (q : b == base G) →
                    ! (ap-idf q) ∙ ! (∙-unit-r (ap (idf (K₂ G η)) q))
                      ==
                    ap2 _∙_ idp (! (ap-idf q) ∙ ! (∙-unit-r (ap (idf (K₂ G η)) q))) ∙
                    ∙-assoc2-!-inv-l-aux (idf (K₂ G η)) q idp idp idp
                  aux2 idp = idp
                  
    abstract
      K₂-map-idf-coher :     
        ∙-ap (K₂-map idf2G) (loop G x) (loop G y) ◃∙
        ap (ap (K₂-map idf2G)) (loop-comp G x y) ◃∙
        (K₂-map-β-pts idf2G (mu x y) ∙
        ! (ap-idf (loop G (mu x y))) ∙
        ! (∙-unit-r (ap (idf (K₂ G η)) (loop G (mu x y))))) ◃∎
          =ₛ
        ap2 _∙_
          (K₂-map-β-pts idf2G x ∙ ! (ap-idf (loop G x)) ∙ ! (∙-unit-r (ap (idf (K₂ G η)) (loop G x))))
          (K₂-map-β-pts idf2G y ∙ ! (ap-idf (loop G y)) ∙ ! (∙-unit-r (ap (idf (K₂ G η)) (loop G y)))) ◃∙
        ∙-assoc2-!-inv-l (idf (K₂ G η)) idp idp (loop G x) (loop G y) ◃∙
        ap (λ p → ap (idf (K₂ G η)) p ∙ idp) (loop-comp G x y) ◃∎
      K₂-map-idf-coher = K₂-map-idf-coher0 x y ∙ₛ (K₂-map-idf-coher1 x y ∙ₛ K₂-map-idf-coher2)

  K₂-map-idf : K₂-map idf2G ∼ idf (K₂ G η)
  K₂-map-idf =
    K₂-∼-ind (K₂-map idf2G) (idf (K₂ G η))
      idp
      (λ x → K₂-map-β-pts idf2G x ∙ ! (ap-idf (loop G x)) ∙ ! (∙-unit-r (ap (idf (K₂ G η)) (loop G x))))
      K₂-map-idf-coher
