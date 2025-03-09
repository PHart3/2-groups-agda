{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import K-hom2-ind
open import KFunctor
open import Delooping
open import LoopK
open import KFunctor-comp
open import SqKLoop
open import apK
open import KLoop-ptr-comp-aux11

module KLoop-ptr-comp where

module _ {i j k} {X : Type i} {Y : Type j} {Z : Type k}
  {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {{ηZ : has-level 2 Z}}
  (x₀ : X) (y₀ : Y) (z₀ : Z) where

  abstract
    KLoop-∘ : (f* : ⊙[ X , x₀ ] ⊙→ ⊙[ Y , y₀ ]) (g* : ⊙[ Y , y₀ ] ⊙→ ⊙[ Z , z₀ ]) →
      !-⊙∼ (sq-KΩ x₀ z₀ (g* ⊙∘ f*)) ∙⊙∼
      ⊙∘-pre (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) (⊙∼-id (g* ⊙∘ f*)) ∙⊙∼
      !-⊙∼ (⊙∘-α-comp g* f* (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) ∙⊙∼ 
      ⊙∘-post g* (sq-KΩ x₀ y₀ f*) ∙⊙∼
      ⊙∘-α-comp g* (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f*)) ∙⊙∼
      ⊙∘-pre (K₂-map⊙ (Loop2Grp-map-str f*)) (sq-KΩ y₀ z₀ g*) ∙⊙∼
      !-⊙∼ (⊙∘-α-comp (K₂-rec-hom z₀ (idf2G {{Loop2Grp z₀}})) (K₂-map⊙ (Loop2Grp-map-str g*)) (K₂-map⊙ (Loop2Grp-map-str f*))) ∙⊙∼
      !-⊙∼  (
        ⊙∘-post (K₂-rec-hom z₀ (idf2G {{Loop2Grp z₀}}))
          (apK₂ (Loop2Grp-map-∘ g* f*) ∙⊙∼ K₂-map-∘ (Loop2Grp-map-str f*) (Loop2Grp-map-str g*)))
        ⊙→∼
      ⊙∼-id (K₂-rec-hom z₀ (idf2G {{Loop2Grp z₀}}) ⊙∘ K₂-map⊙ (Loop2Grp-map-str (g* ⊙∘ f*)))
    fst (KLoop-∘ (f , idp) (g , idp)) = K₂-∼∼-ind idp KLoop-∘-coher-out
      where
        open KLPC-aux11 f g x₀
        abstract
          KLoop-∘-coher-out : (x : x₀ == x₀) →
            hmtpy-nat-∙'
              (λ u →
                ! (fst (sq-KΩ x₀ z₀ (g ∘ f , idp)) u) ∙
                ap g (fst (sq-KΩ x₀ y₀ (f , idp)) u) ∙
                fst (sq-KΩ y₀ z₀ (g , idp)) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp))) u) ∙
                ! (ap (fst (K₂-rec-hom z₀ idf2G))
                    (fst (apK₂ {σ₁ = Loop2Grp-map-str (g ∘ f , idp)} (Loop2Grp-map-∘ (g , idp) (f , idp))) u ∙
                    fst (K₂-map-∘ (Loop2Grp-map-str (f , idp)) (Loop2Grp-map-str (g , idp))) u)))
              (loop (x₀ == x₀) x)
              ==
            hmtpy-nat-∙'
              (λ u → idp {a = fst (K₂-rec-hom z₀ (idf2G {{Loop2Grp z₀}})) (K₂-map (Loop2Grp-map-str (g ∘ f , idp)) u)})
              (loop (x₀ == x₀) x)
          KLoop-∘-coher-out x = =ₛ-out (KLoop-∘-coher x)
    snd (KLoop-∘ (f , idp) (g , idp)) = idp
