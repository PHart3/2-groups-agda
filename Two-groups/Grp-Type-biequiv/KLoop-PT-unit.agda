{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.PtdMap-conv
open import 2Grp
open import 2GrpMap
open import Hmtpy2Grp
open import LoopK-hom
open import KFunctor
open import KFunctor-idf
open import SqKLoop
open import apK
open import KLoop-ptr-idf

-- unit coherence of pseudotransformation from K₂ ∘ Ω to identity

module KLoop-PT-unit where

module _ {i} {X : Ptd i} {{ηX : has-level 2 (de⊙ X)}} where

  private
    τ =
      ⊙-crd∼-to-==
        (⊙∘-lunit (K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}})) ∙⊙∼
        sq-KΩ (pt X) (pt X) (⊙idf X) ∙⊙∼
        ⊙∘-post (K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}}))
          (apK₂ (Loop2Grp-map-idf X) ∙⊙∼ K₂-map-idf {{Loop2Grp (pt X)}})) ◃∎
    ρ₁ =
      ap (λ m → K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}}) ⊙∘ m)
        (ap K₂-action-hom (natiso2G-to-== (Loop2Grp-map-idf X)) ∙
        ⊙-crd∼-to-== (K₂-map-idf {{Loop2Grp (pt X)}}))
    ρ₂ =
      ap (λ m → K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}}) ⊙∘ m)
        (⊙-crd∼-to-==
          {f = K₂-action-hom (Loop2Grp-map (⊙idf X))}
          {g = K₂-action-hom (cohgrphom (idf (pt X == pt X)) {{idf2G {{Loop2Grp (pt X)}}}})}
          (apK₂ {{Loop2Grp (pt X)}} (Loop2Grp-map-idf X)) ∙
        ⊙-crd∼-to-== (K₂-map-idf {{Loop2Grp (pt X)}}))

  abstract
    KLoop-coher-unit-pre :
      ⊙-crd∼-to-== (⊙∘-lunit (K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}}))) ◃∙
      ⊙-crd∼-to-== (sq-KΩ (pt X) (pt X) (⊙idf X)) ◃∙
      ρ₁ ◃∎
        =ₛ
      τ
    KLoop-coher-unit-pre =
      ⊙-crd∼-to-== (⊙∘-lunit (K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}}))) ◃∙
      ⊙-crd∼-to-== (sq-KΩ (pt X) (pt X) (⊙idf X)) ◃∙
      ρ₁ ◃∎
        =ₛ₁⟨ 2 & 1 & ap (ap (λ m → K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}}) ⊙∘ m))
                       (ap (λ v → v ∙ ⊙-crd∼-to-== (K₂-map-idf {{Loop2Grp (pt X)}}))
                         (apK₂-pres (Loop2Grp-map-idf X))) ⟩
      ⊙-crd∼-to-== (⊙∘-lunit (K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}}))) ◃∙
      ⊙-crd∼-to-== (sq-KΩ (pt X) (pt X) (⊙idf X)) ◃∙
      ρ₂ ◃∎
        =ₛ₁⟨ 2 & 1 &
          ⊙-whisk⊙-conv-l-∙ {f₁ = K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}})}
            (apK₂ (Loop2Grp-map-idf X)) (K₂-map-idf {{Loop2Grp (pt X)}}) ⟩
      ⊙-crd∼-to-== (⊙∘-lunit (K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}}))) ◃∙
      ⊙-crd∼-to-== (sq-KΩ (pt X) (pt X) (⊙idf X)) ◃∙
      ⊙-crd∼-to-==
        (⊙∘-post (K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}}))
          (apK₂ (Loop2Grp-map-idf X) ∙⊙∼ K₂-map-idf {{Loop2Grp (pt X)}})) ◃∎
         =ₛ⟨ !ₛ (⊙∘-conv-tri
                  (⊙∘-lunit (K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}})))
                  (sq-KΩ (pt X) (pt X) (⊙idf X))
                  (⊙∘-post (K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}}))
                    (apK₂ (Loop2Grp-map-idf X) ∙⊙∼ K₂-map-idf {{Loop2Grp (pt X)}}))) ⟩
       τ ∎ₛ

  abstract
    KLoop-coher-unit :
      ⊙-crd∼-to-== (⊙∘-lunit (K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}}))) ∙
      ⊙-crd∼-to-== (sq-KΩ (pt X) (pt X) (⊙idf X)) ∙
      ap (λ m → K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}}) ⊙∘ m)
        (ap K₂-action-hom (natiso2G-to-== (Loop2Grp-map-idf X)) ∙
        ⊙-crd∼-to-== (K₂-map-idf {{Loop2Grp (pt X)}}))
        ==
      ⊙-crd∼-to-== (⊙∘-runit (K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}})))
    KLoop-coher-unit = =ₛ-out KLoop-coher-unit-pre ∙ ap ⊙-crd∼-to-== (⊙→∼-to-== (KLoop-idf (pt X)))
