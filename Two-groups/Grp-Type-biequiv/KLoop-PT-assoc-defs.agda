{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import 2Grp
open import 2GrpMap
open import Hmtpy2Grp
open import KFunctor
open import SqKLoop
open import LoopK-hom
open import apK
open import KFunctor-comp

module KLoop-PT-assoc-defs
  {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  {{ηX : has-level 2 (de⊙ X)}} {{ηY : has-level 2 (de⊙ Y)}} {{ηZ : has-level 2 (de⊙ Z)}}
  (f* : X ⊙→ Y) (g* : Y ⊙→ Z) where
  
  υ =
    ⊙-crd∼-to-== (⊙∘-α-crd g* (K₂-rec-hom (pt Y) (idf2G {{Loop2Grp (pt Y)}})) (K₂-action-hom (Loop2Grp-map f*)))
  ρ =
    ! (
      ap (λ m → K₂-rec-hom (pt Z) (idf2G {{Loop2Grp (pt Z)}}) ⊙∘ m)
        (ap K₂-action-hom (natiso2G-to-== (Loop2Grp-map-∘ g* f*)) ∙ ⊙-crd∼-to-== (K₂-map-∘ (Loop2Grp-map-str f*) (Loop2Grp-map-str g*))))
  ζ =
    ! (
      ap (λ m → K₂-rec-hom (pt Z) (idf2G {{Loop2Grp (pt Z)}}) ⊙∘ m)
        ((⊙-crd∼-to-== {f = K₂-action-hom (Loop2Grp-map (g* ⊙∘ f*))} {g = K₂-action-hom (Loop2Grp-map g* ∘2G Loop2Grp-map f*)}
           (apK₂ {{Loop2Grp (pt X)}} {{Loop2Grp (pt Z)}} (Loop2Grp-map-∘ g* f*))) ∙
         ⊙-crd∼-to-== (K₂-map-∘ (Loop2Grp-map-str f*) (Loop2Grp-map-str g*))))
  τ₀ =
    ⊙-crd∼-to-== (!-⊙∼ (sq-KΩ (pt X) (pt Z) (g* ⊙∘ f*))) ◃∙
    ⊙-crd∼-to-== (!-⊙∼ (⊙∘-α-crd g* f* (K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}})))) ◃∙ 
    ⊙-crd∼-to-== (⊙∘-post g* (sq-KΩ (pt X) (pt Y) f*)) ◃∙
    υ ◃∙
    ap (λ m → m ⊙∘ K₂-action-hom (Loop2Grp-map f*)) (⊙-crd∼-to-== (sq-KΩ (pt Y) (pt Z) g*)) ◃∙
    ! (⊙-crd∼-to-==
        (⊙∘-α-crd (K₂-rec-hom (pt Z) (idf2G {{Loop2Grp (pt Z)}})) (K₂-action-hom (Loop2Grp-map g*)) (K₂-action-hom (Loop2Grp-map f*)))) ◃∙
    ρ ◃∎
  τ₁ =
    ⊙-crd∼-to-== (!-⊙∼ (sq-KΩ (pt X) (pt Z) (g* ⊙∘ f*))) ◃∙
    ⊙-crd∼-to-== (!-⊙∼ (⊙∘-α-crd g* f* (K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}})))) ◃∙ 
    ⊙-crd∼-to-== (⊙∘-post g* (sq-KΩ (pt X) (pt Y) f*)) ◃∙
    υ ◃∙
    ⊙-crd∼-to-== (⊙∘-pre (K₂-action-hom (Loop2Grp-map f*)) (sq-KΩ (pt Y) (pt Z) g*)) ◃∙
    ⊙-crd∼-to-== (!-⊙∼
      (⊙∘-α-crd
        (K₂-rec-hom (pt Z) (idf2G {{Loop2Grp (pt Z)}}))
        (K₂-action-hom {{Loop2Grp (pt Y)}} {{Loop2Grp (pt Z)}} (Loop2Grp-map g*))
        (K₂-action-hom {{Loop2Grp (pt X)}} {{Loop2Grp (pt Y)}} (Loop2Grp-map f*)))) ◃∙
    ρ ◃∎
  τ₂ =
    ⊙-crd∼-to-== (!-⊙∼ (sq-KΩ (pt X) (pt Z) (g* ⊙∘ f*))) ◃∙
    ⊙-crd∼-to-== (!-⊙∼ (⊙∘-α-crd g* f* (K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}})))) ◃∙ 
    ⊙-crd∼-to-== (⊙∘-post g* (sq-KΩ (pt X) (pt Y) f*)) ◃∙
    υ ◃∙
    ⊙-crd∼-to-== (⊙∘-pre (K₂-action-hom (Loop2Grp-map f*)) (sq-KΩ (pt Y) (pt Z) g*)) ◃∙
    ⊙-crd∼-to-== (!-⊙∼
      (⊙∘-α-crd (K₂-rec-hom (pt Z) (idf2G {{Loop2Grp (pt Z)}})) (K₂-action-hom (Loop2Grp-map g*))
        (K₂-action-hom {{Loop2Grp (pt X)}} {{Loop2Grp (pt Y)}} (Loop2Grp-map f*)))) ◃∙
    ζ ◃∎
  τ₃ =
    ⊙-crd∼-to-== (!-⊙∼ (sq-KΩ (pt X) (pt Z) (g* ⊙∘ f*))) ◃∙
    ⊙-crd∼-to-== (!-⊙∼ (⊙∘-α-crd g* f* (K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}})))) ◃∙ 
    ⊙-crd∼-to-== (⊙∘-post g* (sq-KΩ (pt X) (pt Y) f*)) ◃∙
    υ ◃∙
    ⊙-crd∼-to-== (⊙∘-pre (K₂-action-hom (Loop2Grp-map f*)) (sq-KΩ (pt Y) (pt Z) g*)) ◃∙
    ⊙-crd∼-to-== (!-⊙∼
      (⊙∘-α-crd (K₂-rec-hom (pt Z) (idf2G {{Loop2Grp (pt Z)}})) (K₂-action-hom (Loop2Grp-map g*)) (K₂-action-hom (Loop2Grp-map f*)))) ◃∙
    ⊙-crd∼-to-==
      {f = K₂-rec-hom (pt Z) (idf2G {{Loop2Grp (pt Z)}}) ⊙∘ K₂-action-hom (Loop2Grp-map g*) ⊙∘ K₂-action-hom (Loop2Grp-map f*)}
      {g = K₂-rec-hom (pt Z) (idf2G {{Loop2Grp (pt Z)}}) ⊙∘ K₂-action-hom (Loop2Grp-map (g* ⊙∘ f*))}
      (!-⊙∼ (
        ⊙∘-post (K₂-rec-hom (pt Z) (idf2G {{Loop2Grp (pt Z)}}))
          (apK₂ {{Loop2Grp (pt X)}} {{Loop2Grp (pt Z)}} (Loop2Grp-map-∘ g* f*) ∙⊙∼ K₂-map-∘ (Loop2Grp-map-str f*) (Loop2Grp-map-str g*)))) ◃∎
  τ₄ =
    ⊙-crd∼-to-== (
      !-⊙∼ (sq-KΩ (pt X) (pt Z) (g* ⊙∘ f*)) ∙⊙∼
      !-⊙∼ (⊙∘-α-crd g* f* (K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}}))) ∙⊙∼
      ⊙∘-post g* (sq-KΩ (pt X) (pt Y) f*) ∙⊙∼
      ⊙∘-α-crd g* (K₂-rec-hom (pt Y) (idf2G {{Loop2Grp (pt Y)}})) (K₂-action-hom {{Loop2Grp (pt X)}} {{Loop2Grp (pt Y)}} (Loop2Grp-map f*)) ∙⊙∼
      ⊙∘-pre (K₂-action-hom (Loop2Grp-map f*)) (sq-KΩ (pt Y) (pt Z) g*) ∙⊙∼
      !-⊙∼ (⊙∘-α-crd (K₂-rec-hom (pt Z) (idf2G {{Loop2Grp (pt Z)}})) (K₂-action-hom (Loop2Grp-map g*)) (K₂-action-hom (Loop2Grp-map f*))) ∙⊙∼
      !-⊙∼ (
        ⊙∘-post (K₂-rec-hom (pt Z) (idf2G {{Loop2Grp (pt Z)}}))
          (apK₂ {σ₁ = Loop2Grp-map-str (g* ⊙∘ f*)} {σ₂ = Loop2Grp-map g* ∘2Gσ Loop2Grp-map f*}
            (Loop2Grp-map-∘ g* f*) ∙⊙∼ K₂-map-∘ (Loop2Grp-map-str f*) (Loop2Grp-map-str g*)))) ◃∎
  τ₅ = ⊙-crd∼-to-== (⊙∼-id (K₂-rec-hom (pt Z) (idf2G {{Loop2Grp (pt Z)}}) ⊙∘ K₂-action-hom (Loop2Grp-map (g* ⊙∘ f*)))) ◃∎
