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
open import KLoop-PT-assoc-aux0
open import KLoop-PT-assoc-aux1

-- associativity coherence of pseudotransformation from K₂ ∘ Ω to identity

module KLoop-PT-assoc where

module _ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  {{ηX : has-level 2 (de⊙ X)}} {{ηY : has-level 2 (de⊙ Y)}} {{ηZ : has-level 2 (de⊙ Z)}}
  (f* : X ⊙→ Y) (g* : Y ⊙→ Z) where

  open KL-PT-aux0 f* g*
  open KL-PT-aux1 f* g*

  abstract
    KLoop-coher-assoc :
      ! (⊙-crd∼-to-== (sq-KΩ (pt X) (pt Z) (g* ⊙∘ f*))) ∙
      ! (⊙-crd∼-to-== (⊙∘-α-comp g* f* (K₂-rec-hom (pt X) (idf2G {{Loop2Grp (pt X)}})))) ∙ 
      ap (λ m → g* ⊙∘ m) (⊙-crd∼-to-== (sq-KΩ (pt X) (pt Y) f*)) ∙
      ⊙-crd∼-to-== (⊙∘-α-comp g* (K₂-rec-hom (pt Y) (idf2G {{Loop2Grp (pt Y)}})) (K₂-action-hom (Loop2Grp-map f*))) ∙
      ap (λ m → m ⊙∘ K₂-action-hom (Loop2Grp-map f*)) (⊙-crd∼-to-== (sq-KΩ (pt Y) (pt Z) g*)) ∙
      ! (⊙-crd∼-to-==
          (⊙∘-α-comp (K₂-rec-hom (pt Z) (idf2G {{Loop2Grp (pt Z)}})) (K₂-action-hom (Loop2Grp-map g*))
            (K₂-action-hom {{Loop2Grp (pt X)}} {{Loop2Grp (pt Y)}} (Loop2Grp-map f*)))) ∙
      ! (
        ap (λ m → K₂-rec-hom (pt Z) (idf2G {{Loop2Grp (pt Z)}}) ⊙∘ m)
          (ap K₂-action-hom (natiso2G-to-== (Loop2Grp-map-∘ g* f*)) ∙ ⊙-crd∼-to-== (K₂-map-∘ (Loop2Grp-map-str f*) (Loop2Grp-map-str g*))))
        ==
      idp {a = K₂-rec-hom (pt Z) (idf2G {{Loop2Grp (pt Z)}}) ⊙∘ K₂-action-hom (Loop2Grp-map (g* ⊙∘ f*))}
    KLoop-coher-assoc = =ₛ-out $
      KLoop-coher-assoc0 ∙ₛ KLoop-coher-assoc1 ∙ₛ KLoop-coher-assoc2 ∙ₛ KLoop-coher-assoc3 ∙ₛ KLoop-coher-assoc4 ∙ₛ KLoop-coher-assoc5
