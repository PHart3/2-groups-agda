{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import 2Grp
open import Hmtpy2Grp
open import Delooping
open import KFunctor
open import LoopK
open import SqKLoop
open import KFunctor-idf
open import apK

module KLoop-ptr-idf-aux2
  {i} {X : Type i} {{ηX : has-level 2 X}} (x₀ : X) (x : x₀ == x₀) where

  open import KLoop-ptr-idf-defs x₀ x

  abstract

    KLoop-ptr-idf-coher2-aux : {b : _} (τ : _ == b) →
      ! (ap (ap (K₂-rec-y₀ x₀ x₀)) τ) ◃∙
      ! (ap-∘ (K₂-rec-y₀ x₀ x₀) (K₂-map (Loop2Grp-map-str (⊙idf ⊙[ X , x₀ ]))) (loop (x₀ == x₀) x)) ◃∙
      ap (λ q → q) (ap-∘ (fst (K₂-rec-hom x₀ idf2G)) (K₂-map (Loop2Grp-map-str (⊙idf ⊙[ X , x₀ ]))) (loop (x₀ == x₀) x)) ◃∙
      ap (ap (fst (K₂-rec-hom x₀ idf2G))) τ ◃∎
        =ₛ
      idp ◃∎
    KLoop-ptr-idf-coher2-aux idp =
      let
        t = ap-∘ (K₂-rec-y₀ x₀ x₀) (K₂-map (Loop2Grp-map-str (⊙idf ⊙[ X , x₀ ]))) (loop (x₀ == x₀) x) in
      =ₛ-in (ap (λ p → ! t ∙ p) (∙-unit-r _ ∙ ap-idf _) ∙ !-inv-l t)

    KLoop-ptr-idf-coher3-aux-a2 : {b : x₀ == x₀} (τ : b == x) →
      ap (ap (idf X)) τ ∙
      ap (λ z → z) (ap-idf x) ∙
      ! τ
        ==
      ap-idf b
    KLoop-ptr-idf-coher3-aux-a2 idp = ∙-unit-r (ap (λ z → z) (ap-idf x)) ∙ ap-idf (ap-idf x) 

    KLoop-ptr-idf-coher3-aux-a :
      ap (ap (idf X)) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x) ◃∙
      ! (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) (ap (idf X) x)) ◃∎
        =ₛ
      ap-idf (ap (K₂-rec-x₀ x₀ x₀) (loop (x₀ == x₀) x)) ◃∙
      ap (λ z → ap (K₂-rec-x₀ x₀ x₀) (loop (x₀ == x₀) z)) (! (ap-idf x)) ◃∎
    KLoop-ptr-idf-coher3-aux-a =
      ap (ap (idf X)) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x) ◃∙
      ! (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) (ap (idf X) x)) ◃∎
        =ₛ⟨ 1 & 1 & hmtpy-nat-!◃ (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}})) (ap-idf x) ⟩
      ap (ap (idf X)) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x) ◃∙
      ap (λ z → z) (ap-idf x) ◃∙
      ! (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x) ◃∙
      ! (ap (λ z → ap (fst (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) (loop (x₀ == x₀) z)) (ap-idf x)) ◃∎
        =ₛ₁⟨ 0 & 3 & KLoop-ptr-idf-coher3-aux-a2 (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x) ⟩
      ap-idf (ap (fst (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) (loop (x₀ == x₀) x)) ◃∙
      ! (ap (λ z → ap (fst (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) (loop (x₀ == x₀) z)) (ap-idf x)) ◃∎
        =ₛ₁⟨ 1 & 1 & !-ap (λ z → ap (K₂-rec-x₀ x₀ x₀) (loop (x₀ == x₀) z)) (ap-idf x) ⟩
      ap-idf (ap (K₂-rec-x₀ x₀ x₀) (loop (x₀ == x₀) x)) ◃∙
      ap (λ z → ap (K₂-rec-x₀ x₀ x₀) (loop (x₀ == x₀) z)) (! (ap-idf x)) ◃∎ ∎ₛ

    KLoop-ptr-idf-coher3-aux-b : {b : _} (p : b == base (x₀ == x₀)) →
      ap-∘ (idf X) (K₂-rec-x₀ x₀ x₀) p ∙
      ap-idf (ap (K₂-rec-x₀ x₀ x₀) p) ∙
      ap (ap (fst (K₂-rec-hom x₀ idf2G))) (! (ap-idf p)) ∙
      ap (λ q → q) (ap (λ q → q) (∘-ap (fst (K₂-rec-hom x₀ idf2G)) (λ z → z) p)) ∙
      idp
        ==
      hmtpy-nat-∙' (λ z → idp) p
    KLoop-ptr-idf-coher3-aux-b idp = idp

  abstract
    KLoop-ptr-idf-coher1 : Λ₁ =ₛ Λ₂
    KLoop-ptr-idf-coher1 = 
      Λ₁
        =ₛ₁⟨ 8 & 2 & ap-!-inv-l (ap (fst (K₂-rec-hom x₀ idf2G))) (K₂-map-β-pts (idf2G {{Loop2Grp x₀}}) x) ⟩
      Λ₂ ∎ₛ

    KLoop-ptr-idf-coher2 : Λ₂ =ₛ Λ₃
    KLoop-ptr-idf-coher2 = 
      Λ₂
        =ₛ⟨ 3 & 4 & KLoop-ptr-idf-coher2-aux (K₂-map-β-pts (Loop2Grp-map-str (⊙idf ⊙[ X , x₀ ])) x) ⟩
      Λ₃ ∎ₛ

    KLoop-ptr-idf-coher3 :
      Λ₃
        =ₛ
      hmtpy-nat-∙' (λ z → idp) (loop (x₀ == x₀) x) ◃∎
    KLoop-ptr-idf-coher3 =
      Λ₃
        =ₛ⟨ 1 & 2 & KLoop-ptr-idf-coher3-aux-a ⟩
      ap-∘ (idf X) (K₂-rec-x₀ x₀ x₀) (loop (x₀ == x₀) x) ◃∙
      ap-idf (ap (K₂-rec-x₀ x₀ x₀) (loop (x₀ == x₀) x)) ◃∙
      ap (λ z → ap (K₂-rec-x₀ x₀ x₀) (loop (x₀ == x₀) z)) (! (ap-idf x)) ◃∙
      idp ◃∙
      ap (ap (fst (K₂-rec-hom x₀ idf2G))) (ap (loop (x₀ == x₀)) (ap-idf x)) ◃∙
      idp ◃∙
      ap (ap (fst (K₂-rec-hom x₀ idf2G))) (! (ap-idf (loop (x₀ == x₀) x))) ◃∙
      idp ◃∙
      idp ◃∙
      ap (λ q → q) (ap (λ q → q) (∘-ap (fst (K₂-rec-hom x₀ idf2G)) (λ z → z) (loop (x₀ == x₀) x))) ◃∙
      idp ◃∎
        =ₛ₁⟨ 2 & 3 & lemma (ap-idf x) ⟩
      ap-∘ (idf X) (K₂-rec-x₀ x₀ x₀) (loop (x₀ == x₀) x) ◃∙
      ap-idf (ap (K₂-rec-x₀ x₀ x₀) (loop (x₀ == x₀) x)) ◃∙
      idp ◃∙
      idp ◃∙
      ap (ap (fst (K₂-rec-hom x₀ idf2G))) (! (ap-idf (loop (x₀ == x₀) x))) ◃∙
      idp ◃∙
      idp ◃∙
      ap (λ q → q) (ap (λ q → q) (∘-ap (fst (K₂-rec-hom x₀ idf2G)) (λ z → z) (loop (x₀ == x₀) x))) ◃∙
      idp ◃∎
        =ₛ₁⟨ KLoop-ptr-idf-coher3-aux-b (loop (x₀ == x₀) x) ⟩
      hmtpy-nat-∙' (λ z → idp) (loop (x₀ == x₀) x) ◃∎ ∎ₛ
        where
          lemma : {b : _} (p : b == x) →
            ap (λ z → ap (K₂-rec-x₀ x₀ x₀) (loop (x₀ == x₀) z)) (! p) ∙
            ap (ap (fst (K₂-rec-hom x₀ idf2G))) (ap (loop (x₀ == x₀)) p)
              ==
            idp
          lemma idp = idp

  open import KLoop-ptr-idf-aux1 x₀ x

  abstract
    KLoop-ptr-idf-coher :
      hmtpy-nat-∙'
        (λ z →
           fst (sq-KΩ x₀ x₀ (⊙idf ⊙[ X , x₀ ])) z ∙
           ap (fst (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})))
             (fst (apK₂ (Loop2Grp-map-idf ⊙[ X , x₀ ])) z ∙ fst (K₂-map-idf {{Loop2Grp x₀}}) z))
        (loop (x₀ == x₀) x)
        ==
      hmtpy-nat-∙' (λ z → idp) (loop (x₀ == x₀) x)
    KLoop-ptr-idf-coher = =ₛ-out $
      KLoop-ptr-idf-coher0 ∙ₛ (KLoop-ptr-idf-coher1 ∙ₛ (KLoop-ptr-idf-coher2 ∙ₛ KLoop-ptr-idf-coher3))
