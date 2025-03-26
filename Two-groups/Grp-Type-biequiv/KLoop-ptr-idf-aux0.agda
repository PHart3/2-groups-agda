{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import K-hom-ind
open import Delooping
open import LoopK-hom
open import KFunctor-idf
open import SqKLoop
open import apK

module KLoop-ptr-idf-aux0
  {i} {X : Type i} {{ηX : has-level 2 X}} (x₀ : X) (x : x₀ == x₀) where

  private
    ν₁ =
      (λ v →
        ap-∘ (idf X) (K₂-rec-x₀ x₀ x₀) (loop (x₀ == x₀) v) ∙
        ap (ap (idf X)) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) v) ∙
        ! (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) (ap (idf X) v)) ∙
        ! (ap (ap (K₂-rec-y₀ x₀ x₀)) (K₂-map-β-pts (Loop2Grp-map-str (idf X , idp)) v)) ∙
        ! (ap-∘ (K₂-rec-y₀ x₀ x₀) (K₂-map (Loop2Grp-map-str (idf X , idp))) (loop (x₀ == x₀) v)))
    ν₂ =
      (λ v →
        K₂-map-β-pts (Loop2Grp-map-str (idf X , idp)) v ∙
        ap (loop (x₀ == x₀)) (ap-idf v) ∙
        ! (K₂-map-β-pts (idf2G {{Loop2Grp x₀}}) v))

  abstract

    K₂-β-1 :
      hmtpy-nat-∙' (fst (sq-KΩ x₀ x₀ (⊙idf ⊙[ X , x₀ ]))) (loop (x₀ == x₀) x) ◃∎
        =ₛ
      ap-∘ (idf X) (K₂-rec-x₀ x₀ x₀) (loop (x₀ == x₀) x) ◃∙
      ap (ap (idf X)) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x) ◃∙
      ! (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) (ap (idf X) x)) ◃∙
      ! (ap (ap (K₂-rec-y₀ x₀ x₀)) (K₂-map-β-pts (Loop2Grp-map-str (idf X , idp)) x)) ◃∙
      ! (ap-∘ (K₂-rec-y₀ x₀ x₀) (K₂-map (Loop2Grp-map-str (idf X , idp))) (loop (x₀ == x₀) x)) ◃∎
    K₂-β-1 = =ₛ-in $
      K₂-∼-ind-β
        (K₂-rec-x₀ x₀ x₀)
        (K₂-rec-y₀ x₀ x₀ ∘ K₂-map (Loop2Grp-map-str (idf X , idp)))
        idp
        ν₁
        _ x

    K₂-β-2 :
      hmtpy-nat-∙' (fst (apK₂ (Loop2Grp-map-idf ⊙[ X , x₀ ]))) (loop (x₀ == x₀) x) ◃∎
        =ₛ
      K₂-map-β-pts (Loop2Grp-map-str (idf X , idp)) x ◃∙
      ap (loop (x₀ == x₀)) (ap-idf x) ◃∙
      ! (K₂-map-β-pts (idf2G {{Loop2Grp x₀}}) x) ◃∎
    K₂-β-2 = =ₛ-in $
      K₂-∼-ind-β
        (K₂-map (Loop2Grp-map-str (idf X , idp)))
        (K₂-map (idf2G {{Loop2Grp x₀}}))
        idp
        ν₂
        _ x

    K₂-β-3 :
      hmtpy-nat-∙' (fst (K₂-map-idf {{Loop2Grp x₀}})) (loop (x₀ == x₀) x) ◃∎
        =ₛ
      K₂-map-β-pts (idf2G {{Loop2Grp x₀}}) x ◃∙
      ! (ap-idf (loop (x₀ == x₀) x)) ◃∎
    K₂-β-3 = =ₛ-in $
      K₂-∼-ind-β
        (K₂-map (idf2G {{Loop2Grp x₀}}))
        (idf (K₂ (x₀ == x₀) (Loop2Grp x₀)))
        idp
        (λ v →
          K₂-map-β-pts (idf2G {{Loop2Grp x₀}}) v ∙ ! (ap-idf (loop (x₀ == x₀) v)))
        _ x
        
        
