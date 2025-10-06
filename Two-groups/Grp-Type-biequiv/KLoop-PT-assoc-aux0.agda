{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.PtdMap-conv
open import 2Grp
open import 2GrpMap
open import Hmtpy2Grp
open import KFunctor
open import SqKLoop
open import LoopK-hom
open import apK
open import KFunctor-comp

module KLoop-PT-assoc-aux0 where

module KL-PT-aux0 {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  {{ηX : has-level 2 (de⊙ X)}} {{ηY : has-level 2 (de⊙ Y)}} {{ηZ : has-level 2 (de⊙ Z)}}
  (f* : X ⊙→ Y) (g* : Y ⊙→ Z) where

  open import KLoop-PT-assoc-defs f* g*
 
  abstract

    KLoop-coher-assoc0 :
      ! (⊙-crd∼-to-== (sq-KΩ (pt X) (pt Z) (g* ⊙∘ f*))) ◃∙
      ! (⊙-crd∼-to-== (⊙∘-α-comp g* f* (K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}})))) ◃∙ 
      ap (λ m → g* ⊙∘ m) (⊙-crd∼-to-== (sq-KΩ (pt X) (pt Y) f*)) ◃∙
      υ ◃∙
      ap (λ m → m ⊙∘ K₂-action-hom (Loop2Grp-map f*)) (⊙-crd∼-to-== (sq-KΩ (pt Y) (pt Z) g*)) ◃∙
      ! (⊙-crd∼-to-==
          (⊙∘-α-comp (K₂-rec-hom (pt Z) (idf2G {{Loop2Grp (pt Z)}})) (K₂-action-hom (Loop2Grp-map g*)) (K₂-action-hom (Loop2Grp-map f*)))) ◃∙
      ρ ◃∎
        =ₛ
      τ₀
    KLoop-coher-assoc0 =
      ! (⊙-crd∼-to-== (sq-KΩ (pt X) (pt Z) (g* ⊙∘ f*))) ◃∙
      ! (⊙-crd∼-to-== (⊙∘-α-comp g* f* (K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}})))) ◃∙ 
      ap (λ m → g* ⊙∘ m) (⊙-crd∼-to-== (sq-KΩ (pt X) (pt Y) f*)) ◃∙
      υ ◃∙
      ap (λ m → m ⊙∘ K₂-action-hom (Loop2Grp-map f*)) (⊙-crd∼-to-== (sq-KΩ (pt Y) (pt Z) g*)) ◃∙
      ! (⊙-crd∼-to-==
          (⊙∘-α-comp (K₂-rec-hom (pt Z) (idf2G {{Loop2Grp (pt Z)}})) (K₂-action-hom (Loop2Grp-map g*)) (K₂-action-hom (Loop2Grp-map f*)))) ◃∙
      ρ ◃∎
        =ₛ₁⟨ 0 & 1 & ! (!⊙-conv (sq-KΩ (pt X) (pt Z) (g* ⊙∘ f*))) ⟩
      ⊙-crd∼-to-== (!-⊙∼ (sq-KΩ (pt X) (pt Z) (g* ⊙∘ f*))) ◃∙
      ! (⊙-crd∼-to-== (⊙∘-α-comp g* f* (K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}})))) ◃∙ 
      ap (λ m → g* ⊙∘ m) (⊙-crd∼-to-== (sq-KΩ (pt X) (pt Y) f*)) ◃∙
      υ ◃∙
      ap (λ m → m ⊙∘ K₂-action-hom (Loop2Grp-map f*)) (⊙-crd∼-to-== (sq-KΩ (pt Y) (pt Z) g*)) ◃∙
      ! (⊙-crd∼-to-==
          (⊙∘-α-comp (K₂-rec-hom (pt Z) (idf2G {{Loop2Grp (pt Z)}})) (K₂-action-hom (Loop2Grp-map g*)) (K₂-action-hom (Loop2Grp-map f*)))) ◃∙
      ρ ◃∎
        =ₛ₁⟨ 1 & 1 & ! (!⊙-conv (⊙∘-α-comp g* f* (K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}})))) ⟩
      ⊙-crd∼-to-== (!-⊙∼ (sq-KΩ (pt X) (pt Z) (g* ⊙∘ f*))) ◃∙
      ⊙-crd∼-to-== (!-⊙∼ (⊙∘-α-comp g* f* (K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}})))) ◃∙ 
      ap (λ m → g* ⊙∘ m) (⊙-crd∼-to-== (sq-KΩ (pt X) (pt Y) f*)) ◃∙
      υ ◃∙
      ap (λ m → m ⊙∘ K₂-action-hom (Loop2Grp-map f*)) (⊙-crd∼-to-== (sq-KΩ (pt Y) (pt Z) g*)) ◃∙
      ! (⊙-crd∼-to-==
          (⊙∘-α-comp (K₂-rec-hom (pt Z) (idf2G {{Loop2Grp (pt Z)}})) (K₂-action-hom (Loop2Grp-map g*)) (K₂-action-hom (Loop2Grp-map f*)))) ◃∙
      ρ ◃∎
        =ₛ₁⟨ 2 & 1 & ! (whisk⊙-conv-l (sq-KΩ (pt X) (pt Y) f*)) ⟩
      τ₀ ∎ₛ

    KLoop-coher-assoc1 : τ₀ =ₛ τ₁
    KLoop-coher-assoc1 = 
      τ₀
        =ₛ₁⟨ 4 & 1 & ! (whisk⊙-conv-r (sq-KΩ (pt Y) (pt Z) g*)) ⟩
      ⊙-crd∼-to-== (!-⊙∼ (sq-KΩ (pt X) (pt Z) (g* ⊙∘ f*))) ◃∙
      ⊙-crd∼-to-== (!-⊙∼ (⊙∘-α-comp g* f* (K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}})))) ◃∙ 
      ⊙-crd∼-to-== (⊙∘-post g* (sq-KΩ (pt X) (pt Y) f*)) ◃∙
      υ ◃∙
      ⊙-crd∼-to-== (⊙∘-pre (K₂-action-hom (Loop2Grp-map f*)) (sq-KΩ (pt Y) (pt Z) g*)) ◃∙
      ! (⊙-crd∼-to-==
          (⊙∘-α-comp (K₂-rec-hom (pt Z) (idf2G {{Loop2Grp (pt Z)}})) (K₂-action-hom (Loop2Grp-map g*)) (K₂-action-hom (Loop2Grp-map f*)))) ◃∙
      ρ ◃∎
        =ₛ₁⟨ 5 & 1 & ! (!⊙-conv (⊙∘-α-comp (K₂-rec-hom (pt Z) (idf2G {{Loop2Grp (pt Z)}})) (K₂-action-hom (Loop2Grp-map g*)) (K₂-action-hom (Loop2Grp-map f*)))) ⟩
      τ₁ ∎ₛ
      
    KLoop-coher-assoc2 : τ₁ =ₛ τ₃
    KLoop-coher-assoc2 = 
      τ₁
        =ₛ₁⟨ 6 & 1 &
          ap (λ v →
               ! (ap (λ m → K₂-rec-hom (pt Z) (idf2G {{Loop2Grp (pt Z)}}) ⊙∘ m)
                   (v ∙ ⊙-crd∼-to-== (K₂-map-∘ (Loop2Grp-map-str f*) (Loop2Grp-map-str g*)))))
            (apK₂-pres (Loop2Grp-map-∘ g* f*)) ⟩
      τ₂
        =ₛ₁⟨ 6 & 1 &
          !⊙-whisk⊙-conv-l-∙ {f₁ = K₂-rec-hom (pt Z) (idf2G {{Loop2Grp (pt Z)}})}
            (apK₂ (Loop2Grp-map-∘ g* f*)) (K₂-map-∘ (Loop2Grp-map-str f*) (Loop2Grp-map-str g*)) ⟩
      τ₃ ∎ₛ

    KLoop-coher-assoc3 : τ₃ =ₛ τ₄
    KLoop-coher-assoc3 =
      ⊙∘-conv-sept
        (!-⊙∼ (sq-KΩ (pt X) (pt Z) (g* ⊙∘ f*)))
        (!-⊙∼ (⊙∘-α-comp g* f* (K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}}))))
        (⊙∘-post g* (sq-KΩ (pt X) (pt Y) f*))
        (⊙∘-α-comp g* (K₂-rec-hom (pt Y) (idf2G {{Loop2Grp (pt Y)}})) (K₂-action-hom (Loop2Grp-map f*)))
        (⊙∘-pre (K₂-action-hom (Loop2Grp-map f*)) (sq-KΩ (pt Y) (pt Z) g*))
        (!-⊙∼ (⊙∘-α-comp (K₂-rec-hom (pt Z) (idf2G {{Loop2Grp (pt Z)}})) (K₂-action-hom (Loop2Grp-map g*))
          (K₂-action-hom {{Loop2Grp (pt X)}} {{Loop2Grp (pt Y)}} (Loop2Grp-map f*))))
        (!-⊙∼ (
          ⊙∘-post (K₂-rec-hom (pt Z) (idf2G {{Loop2Grp (pt Z)}}))
            (apK₂ (Loop2Grp-map-∘ g* f*) ∙⊙∼ K₂-map-∘ (Loop2Grp-map-str f*) (Loop2Grp-map-str g*))))
