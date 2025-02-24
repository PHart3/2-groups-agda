{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics
open import 2Grp
open import Delooping
open import K-hom-ind
open import KFunctor

module KFunctor-idf-aux2 where

open CohGrp {{...}}

module _ {i} {G : Type i} {{η : CohGrp G}} where

  module _ (x y : G) where

    K₂-map-idf-coher2 =
      idp ◃∙
      ap2 _∙_ (K₂-map-β-pts idf2G x) (K₂-map-β-pts idf2G y) ◃∙
      idp ◃∙
      ! (ap-idf (loop G x ∙ loop G y)) ◃∙
      ap (λ p → ap (idf (K₂ G η)) p) (loop-comp G x y) ◃∎
        =ₑ⟨ 0 & 4 &
          (ap2 _∙_
            (K₂-map-β-pts idf2G x ∙ ! (ap-idf (loop G x)))
            (K₂-map-β-pts idf2G y ∙ ! (ap-idf (loop G y))) ◃∙
          ∙-assoc2-!-inv-l (idf (K₂ G η)) idp idp (loop G x) (loop G y) ◃∎)
          % =ₛ-in (lemma (K₂-map-β-pts idf2G x) (K₂-map-β-pts idf2G y)) ⟩
      ap2 _∙_
        (K₂-map-β-pts idf2G x ∙ ! (ap-idf (loop G x)))
        (K₂-map-β-pts idf2G y ∙ ! (ap-idf (loop G y))) ◃∙
      ∙-assoc2-!-inv-l (idf (K₂ G η)) idp idp (loop G x) (loop G y) ◃∙
      ap (λ p → ap (idf (K₂ G η)) p) (loop-comp G x y) ◃∎ ∎ₛ
        where
          lemma : {p₃ p₄ : base G == base G}
            (p₁ : ap (K₂-map idf2G) (loop G x) == p₃)
            (p₂ : ap (K₂-map idf2G) (loop G y) == p₄) →
            ap2 _∙_ p₁ p₂ ∙
            ! (ap-idf (p₃ ∙ p₄))
              ==
            ap2 _∙_ (p₁ ∙ ! (ap-idf p₃)) (p₂ ∙ ! (ap-idf p₄)) ∙
            ∙-assoc2-!-inv-l (idf (K₂ G η)) idp idp p₃ p₄
          lemma idp idp = aux (ap (K₂-map idf2G) (loop G x)) (ap (K₂-map idf2G) (loop G y))
            where
              aux : {b : K₂ G η} (q₁ : base G == b) (q₂ : b == base G) →
                ! (ap-idf (q₁ ∙ q₂))
                  ==
                ap2 _∙_ (! (ap-idf q₁)) (! (ap-idf q₂)) ∙
                ∙-assoc2-!-inv-l (idf (K₂ G η)) idp idp q₁ q₂
              aux idp q₂ = aux2 q₂
                where
                  aux2 : {b : K₂ G η} (q : b == base G) →
                    ! (ap-idf q)
                      ==
                    ap2 _∙_ idp (! (ap-idf q)) ∙
                    ∙-assoc2-!-inv-l-aux (idf (K₂ G η)) q idp idp idp
                  aux2 idp = idp
