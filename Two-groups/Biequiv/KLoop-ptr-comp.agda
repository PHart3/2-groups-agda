{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import K-hom-ind
open import KFunctor
open import Delooping
open import LoopK
open import KFunctor-comp
open import SqKLoop

module KLoop-ptr-comp where

module _ {i j k} {X : Type i} {Y : Type j} {Z : Type k}
  {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {{ηZ : has-level 2 Z}}
  (x₀ : X) (y₀ : Y) (z₀ : Z) where
{-
  private  
    Λx₀ = wkmag-to-loop x₀ (cohmaghom (idf (x₀ == x₀)) {{idf2G}})
    Λy₀ = wkmag-to-loop y₀ (cohmaghom (idf (y₀ == y₀)) {{idf2G}})
    Λz₀ = wkmag-to-loop z₀ (cohmaghom (idf (z₀ == z₀)) {{idf2G}})
    K₂-rec-x₀ = K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)
    K₂-rec-y₀ = K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)
    K₂-rec-z₀ = K₂-rec (z₀ == z₀) z₀ (loop' Λz₀) (loop-comp' Λz₀) (loop-assoc' Λz₀)
-}
    KLoop-∘ : (f* : ⊙[ X , x₀ ] ⊙→ ⊙[ Y , y₀ ]) (g* : ⊙[ Y , y₀ ] ⊙→ ⊙[ Z , z₀ ]) →
      !-⊙∼ (sq-KΩ x₀ z₀ (g* ⊙∘ f*)) ∙⊙∼
      ⊙∘-pre (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) (⊙∼-id (g* ⊙∘ f*)) ∙⊙∼
      ⊙∘-assoc-comp g* f* (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∙⊙∼ 
      ⊙∘-post g* (sq-KΩ x₀ y₀ f*) ∙⊙∼
      !-⊙∼ (⊙∘-assoc-comp g* (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f*))) ∙⊙∼
      ⊙∘-pre (K₂-map⊙ (Loop2Grp-map-str f*)) (sq-KΩ y₀ z₀ g*) ∙⊙∼
      ⊙∘-assoc-comp (K₂-rec-hom z₀ (idf2G {{Loop2Grp z₀}})) (K₂-map⊙ (Loop2Grp-map-str g*)) (K₂-map⊙ (Loop2Grp-map-str f*)) ∙⊙∼
      !-⊙∼  (
        ⊙∘-post (K₂-rec-hom z₀ (idf2G {{Loop2Grp z₀}}))
          ({!apK₂ (Loop2Grp-map-∘ g* f *)!} ∙⊙∼ K₂-map-∘ (Loop2Grp-map-str f*) (Loop2Grp-map-str g*)))
        ⊙→∼
      ⊙∼-id (K₂-rec-hom z₀ (idf2G {{Loop2Grp z₀}}) ⊙∘ K₂-map⊙ (Loop2Grp-map-str (g* ⊙∘ f*)))
    fst (KLoop-∘ (f , idp) (g , idp)) = {!!}
    snd (KLoop-∘ (f , idp) (g , idp)) = {!!}
