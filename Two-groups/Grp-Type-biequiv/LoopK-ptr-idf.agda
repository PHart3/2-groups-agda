{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=5 --lossy-unification #-}

open import lib.Basics
open import lib.types.LoopSpace
open import 2Semigroup
open import 2SGrpMap
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import K-hom-ind
open import KFunctor-idf
open import Delooping
open import LoopFunctor-ap

module LoopK-ptr-idf where

module _ {i} {G : Type i} {{η : CohGrp G}} (x : G) where

  module LKI-pre where

    abstract
      LoopK-idf-pre :
        (Ω-fmap-ap K₂-map-idf (loop G x) ∙ ap-idf (loop G x)) ◃∎
          =ₛ
        K₂-map-β-pts idf2G x ◃∎
      LoopK-idf-pre =
        (Ω-fmap-ap K₂-map-idf (loop G x) ∙ ap-idf (loop G x)) ◃∎
          =ₛ⟨ =ₛ-in (idp {a = Ω-fmap-ap K₂-map-idf (loop G x) ∙ ap-idf (loop G x)}) ⟩
        Ω-fmap-ap K₂-map-idf (loop G x) ◃∙
        ap-idf (loop G x) ◃∎
          =ₛ⟨ 0 & 1 & Ω-fmap-ap-hnat K₂-map-idf (loop G x) ⟩
        idp ◃∙
        ap (λ q → q)
          (hmtpy-nat-∙'
            (K₂-∼-ind (K₂-map idf2G) (idf (K₂ G η)) idp
              (λ v →  K₂-map-β-pts idf2G v ∙ ! (ap-idf (loop G v))) _)
          (loop G x)) ◃∙
        idp ◃∙
        ap-idf (loop G x) ◃∎
          =ₛ₁⟨ 0 & 2 &
            ap-idf (hmtpy-nat-∙' (K₂-∼-ind (K₂-map idf2G) (idf (K₂ G η)) idp (λ v → K₂-map-β-pts idf2G v ∙ ! (ap-idf (loop G v))) _) (loop G x)) ⟩
        hmtpy-nat-∙' (K₂-∼-ind (K₂-map idf2G) (idf (K₂ G η)) idp (λ v → K₂-map-β-pts idf2G v ∙ ! (ap-idf (loop G v))) _) (loop G x) ◃∙
        idp ◃∙
        ap-idf (loop G x) ◃∎
          =ₑ⟨ 0 & 1 & (K₂-map-β-pts idf2G x ◃∙ ! (ap-idf (loop G x)) ◃∎)
            % =ₛ-in (K₂-∼-ind-β (K₂-map idf2G) (idf (K₂ G η)) idp (λ v →  K₂-map-β-pts idf2G v ∙ ! (ap-idf (loop G v))) _ x) ⟩
        K₂-map-β-pts idf2G x ◃∙
        ! (ap-idf (loop G x)) ◃∙
        idp ◃∙
        ap-idf (loop G x) ◃∎
          =ₛ₁⟨ 1 & 3 & !-inv-l (ap-idf (loop G x)) ⟩
        K₂-map-β-pts idf2G x ◃∙
        idp ◃∎
          =ₛ₁⟨ ∙-unit-r (K₂-map-β-pts idf2G x) ⟩
        K₂-map-β-pts idf2G x ◃∎ ∎ₛ

  open LKI-pre

  private
    γ = ∙-unit-r (K₂-map-β-pts idf2G x)

  abstract
    LoopK-idf :      
      ! (WkSGrpNatIso.θ (Loop2Grp-map-ap K₂-map-idf) (loop G x) ∙ ap-idf (loop G x)) ◃∙
      K₂-map-β-pts idf2G x ◃∙
      idp ◃∎
        =ₛ
      idp ◃∎
    LoopK-idf =
      ! (WkSGrpNatIso.θ (Loop2Grp-map-ap K₂-map-idf) (loop G x) ∙ ap-idf (loop G x)) ◃∙
      K₂-map-β-pts idf2G x ◃∙
      idp ◃∎
        =ₛ₁⟨ 0 & 1 & ap (λ p → ! (p ∙ ap-idf (loop G x))) (Loop2Grp-map-ap-fst K₂-map-idf (loop G x)) ⟩
      ! (Ω-fmap-ap K₂-map-idf (loop G x) ∙ ap-idf (loop G x)) ◃∙
      K₂-map-β-pts idf2G x ◃∙
      idp ◃∎
        =ₛ₁⟨ 1 & 2 & γ ⟩     
      ! (Ω-fmap-ap K₂-map-idf (loop G x) ∙ ap-idf (loop G x)) ◃∙
      K₂-map-β-pts idf2G x ◃∎
        =ₛ₁⟨ 0 & 1 & ap ! (=ₛ-out LoopK-idf-pre) ⟩
      ! (K₂-map-β-pts idf2G x) ◃∙
      K₂-map-β-pts idf2G x ◃∎
        =ₛ₁⟨ !-inv-l (K₂-map-β-pts idf2G x) ⟩
      idp ◃∎ ∎ₛ
