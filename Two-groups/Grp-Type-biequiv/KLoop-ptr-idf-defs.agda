{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import LoopK-hom
open import KFunctor-idf
open import SqKLoop
open import apK

module KLoop-ptr-idf-defs
  {i} {X : Type i} {{ηX : has-level 2 X}} (x₀ : X) (x : x₀ == x₀) where

  Λ₁ = 
    ap-∘ (idf X) (K₂-rec-x₀ x₀ x₀) (loop (x₀ == x₀) x) ◃∙
    ap (ap (idf X)) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x) ◃∙
    ! (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) (ap (idf X) x)) ◃∙
    ! (ap (ap (K₂-rec-y₀ x₀ x₀)) (K₂-map-β-pts (Loop2Grp-map-str (⊙idf ⊙[ X , x₀ ])) x)) ◃∙
    ! (ap-∘ (K₂-rec-y₀ x₀ x₀) (K₂-map (Loop2Grp-map-str (⊙idf ⊙[ X , x₀ ]))) (loop (x₀ == x₀) x)) ◃∙
    ap (λ q → q) (ap-∘ (fst (K₂-rec-hom x₀ idf2G)) (K₂-map (Loop2Grp-map-str (⊙idf ⊙[ X , x₀ ]))) (loop (x₀ == x₀) x)) ◃∙
    ap (ap (fst (K₂-rec-hom x₀ idf2G))) (K₂-map-β-pts (Loop2Grp-map-str (⊙idf ⊙[ X , x₀ ])) x) ◃∙
    ap (ap (fst (K₂-rec-hom x₀ idf2G))) (ap (loop (x₀ == x₀)) (ap-idf x)) ◃∙
    ap (ap (fst (K₂-rec-hom x₀ idf2G))) (! (K₂-map-β-pts (idf2G {{Loop2Grp x₀}}) x)) ◃∙
    ap (ap (fst (K₂-rec-hom x₀ idf2G))) (K₂-map-β-pts idf2G x) ◃∙
    ap (ap (fst (K₂-rec-hom x₀ idf2G))) (! (ap-idf (loop (x₀ == x₀) x))) ◃∙
    idp ◃∙
    idp ◃∙
    ap (λ q → q) (ap (λ q → q) (∘-ap (fst (K₂-rec-hom x₀ idf2G)) (λ z → z) (loop (x₀ == x₀) x))) ◃∙
    idp ◃∎

  Λ₂ = 
    ap-∘ (idf X) (K₂-rec-x₀ x₀ x₀) (loop (x₀ == x₀) x) ◃∙
    ap (ap (idf X)) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x) ◃∙
    ! (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) (ap (idf X) x)) ◃∙
    ! (ap (ap (K₂-rec-y₀ x₀ x₀)) (K₂-map-β-pts (Loop2Grp-map-str (⊙idf ⊙[ X , x₀ ])) x)) ◃∙
    ! (ap-∘ (K₂-rec-y₀ x₀ x₀) (K₂-map (Loop2Grp-map-str (⊙idf ⊙[ X , x₀ ]))) (loop (x₀ == x₀) x)) ◃∙
    ap (λ q → q) (ap-∘ (fst (K₂-rec-hom x₀ idf2G)) (K₂-map (Loop2Grp-map-str (⊙idf ⊙[ X , x₀ ]))) (loop (x₀ == x₀) x)) ◃∙
    ap (ap (fst (K₂-rec-hom x₀ idf2G))) (K₂-map-β-pts (Loop2Grp-map-str (⊙idf ⊙[ X , x₀ ])) x) ◃∙
    ap (ap (fst (K₂-rec-hom x₀ idf2G))) (ap (loop (x₀ == x₀)) (ap-idf x)) ◃∙
    idp ◃∙
    ap (ap (fst (K₂-rec-hom x₀ idf2G))) (! (ap-idf (loop (x₀ == x₀) x))) ◃∙
    idp ◃∙
    idp ◃∙
    ap (λ q → q) (ap (λ q → q) (∘-ap (fst (K₂-rec-hom x₀ idf2G)) (λ z → z) (loop (x₀ == x₀) x))) ◃∙
    idp ◃∎

  Λ₃ = 
    ap-∘ (idf X) (K₂-rec-x₀ x₀ x₀) (loop (x₀ == x₀) x) ◃∙
    ap (ap (idf X)) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x) ◃∙
    ! (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) (ap (idf X) x)) ◃∙
    idp ◃∙
    ap (ap (fst (K₂-rec-hom x₀ idf2G))) (ap (loop (x₀ == x₀)) (ap-idf x)) ◃∙
    idp ◃∙
    ap (ap (fst (K₂-rec-hom x₀ idf2G))) (! (ap-idf (loop (x₀ == x₀) x))) ◃∙
    idp ◃∙
    idp ◃∙
    ap (λ q → q) (ap (λ q → q) (∘-ap (fst (K₂-rec-hom x₀ idf2G)) (λ z → z) (loop (x₀ == x₀) x))) ◃∙
    idp ◃∎
