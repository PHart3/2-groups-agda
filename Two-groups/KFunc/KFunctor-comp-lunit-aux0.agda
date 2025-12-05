{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import 2Semigroup
open import 2SGrpMap
open import 2Grp
open import Delooping
open import K-hom-ind
open import KFunctor
open import KFunctor-idf
open import KFunctor-comp
open import apK

module KFunctor-comp-lunit-aux0 where

module KFCLU0 {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  {f : G₁ → G₂} (σ : WkSGrpHomStr f) (x : G₁) where

  private
    ν₁ =
      λ v →
        K₂-map-β-pts σ v ∙
        (! (K₂-map-β-pts (cohsgrphom (λ z → z) {{idf2G}} ∘2Mσ cohsgrphom f {{σ}}) v) :> (loop G₂ (f v) == ap (K₂-map (cohsgrphom (λ z → z) {{idf2G}} ∘2Mσ cohsgrphom f {{σ}})) (loop G₁ v)))
    ν₂-suff =
      λ v →
        ! (K₂-map-β-pts idf2G (f v)) ∙
        (! (ap (ap (K₂-map idf2G)) (K₂-map-β-pts σ v)) :> (ap (K₂-map idf2G) (loop G₂ (f v)) == ap (K₂-map idf2G) (ap (K₂-map σ) (loop G₁ v)))) ∙
        ∘-ap (K₂-map idf2G) (K₂-map σ) (loop G₁ v)
    ν₂ =
      λ v →
        K₂-map-β-pts (cohsgrphom (λ z → z) {{idf2G}} ∘2Mσ cohsgrphom f {{σ}}) v ∙
        (ν₂-suff v :> (loop G₂ (f v) == ap (K₂-map idf2G ∘ K₂-map σ) (loop G₁ v)))
    ν₃ = λ v → K₂-map-β-pts idf2G v ∙ ! (ap-idf (loop G₂ v))

  abstract

    K₂-β-1 :
      hmtpy-nat-∙' (fst (apK₂ (unit-wksgrphom-l (sgrphom-forg (cohsgrphom f {{σ}}))))) (loop G₁ x) ◃∎
        =ₛ
      K₂-map-β-pts σ x ◃∙
      ! (K₂-map-β-pts (cohsgrphom (λ z → z) {{idf2G}} ∘2Mσ cohsgrphom f {{σ}}) x) ◃∎
    K₂-β-1 = =ₛ-in $
      K₂-∼-ind-β (K₂-map σ) (K₂-map (cohsgrphom (λ z → z) {{idf2G}} ∘2Mσ cohsgrphom f {{σ}}))
        (idp :> (base G₂ == base G₂))
        ν₁
        _ x

    K₂-β-2 :
      hmtpy-nat-∙' (fst (K₂-map-∘ σ idf2G)) (loop G₁ x) ◃∎
        =ₛ
      K₂-map-β-pts (cohsgrphom (λ z → z) {{idf2G}} ∘2Mσ cohsgrphom f {{σ}}) x ◃∙
      ! (K₂-map-β-pts idf2G (f x)) ◃∙
      ! (ap (ap (K₂-map idf2G)) (K₂-map-β-pts σ x)) ◃∙
      ∘-ap (K₂-map idf2G) (K₂-map σ) (loop G₁ x) ◃∎
    K₂-β-2 = =ₛ-in $
      K₂-∼-ind-β
        (map₁-∘ σ idf2G)
        (map₂-∘ σ idf2G)
        (idp :> (base G₂ == base G₂))
        ν₂
        _ x

    K₂-β-3 :
      hmtpy-nat-∙' (fst (K₂-map-idf {{η₂}})) (ap (K₂-map σ) (loop G₁ x)) ◃∎
        =ₛ
      ap (ap (K₂-map idf2G)) (K₂-map-β-pts σ x) ◃∙
      K₂-map-β-pts idf2G (f x) ◃∙
      ! (ap-idf (loop G₂ (f x))) ◃∙
      ! (ap (ap (idf (K₂ G₂ η₂))) (K₂-map-β-pts σ x)) ◃∎
    K₂-β-3 =
      hmtpy-nat-∙' (fst (K₂-map-idf {{η₂}})) (ap (K₂-map σ) (loop G₁ x)) ◃∎
        =ₛ⟨ apCommSq2◃-rev (λ (p : base G₂ == base G₂) → hmtpy-nat-∙' (fst (K₂-map-idf {{η₂}})) p) (K₂-map-β-pts σ x) ⟩
      ap (ap (K₂-map idf2G)) (K₂-map-β-pts σ x) ◃∙
      hmtpy-nat-∙' (fst (K₂-map-idf {{η₂}})) (loop G₂ (f x)) ◃∙
      ! (ap (ap (idf (K₂ G₂ η₂))) (K₂-map-β-pts σ x)) ◃∎
        =ₑ⟨ 1 & 1 & (K₂-map-β-pts idf2G (f x) ◃∙ ! (ap-idf (loop G₂ (f x))) ◃∎)
          % =ₛ-in (K₂-∼-ind-β (K₂-map idf2G) (idf (K₂ G₂ η₂)) idp ν₃ _ (f x)) ⟩
      ap (ap (K₂-map idf2G)) (K₂-map-β-pts σ x) ◃∙
      K₂-map-β-pts idf2G (f x) ◃∙
      ! (ap-idf (loop G₂ (f x))) ◃∙
      ! (ap (ap (idf (K₂ G₂ η₂))) (K₂-map-β-pts σ x)) ◃∎ ∎ₛ
