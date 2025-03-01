{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import K-hom2-ind
open import Delooping
open import LoopK
open import KFunctor-idf
open import SqKLoop
open import apK

module KLoop-ptr-idf where

module _ {i} {X : Type i} {{ηX : has-level 2 X}} (x₀ : X) where

    KLoop-idf :
      ⊙∘-runit (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∙⊙∼
      ⊙∘-pre (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) (⊙∼-id (⊙idf ⊙[ X , x₀ ])) ∙⊙∼
      sq-KΩ x₀ x₀ (⊙idf ⊙[ X , x₀ ]) ∙⊙∼
      ⊙∘-post (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))
        (apK₂ (Loop2Grp-map-idf ⊙[ X , x₀ ]) ∙⊙∼ K₂-map-idf {{Loop2Grp x₀}})
        ⊙→∼
      ⊙∘-lunit (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))
    fst KLoop-idf = K₂-∼∼-ind idp {!!} -- (KLoop-idf-coher-out x₀)
    snd KLoop-idf = =ₛ-in idp


{-
(x : x₀ == x₀) →
hmtpy-nat-∙'
(λ z →
   fst
   (sq-KΩ x₀ x₀ (⊙idf ⊙[ X , x₀ ])) z ∙
   fst (⊙∘-post (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))
    (apK₂ (Loop2Grp-map-idf ⊙[ X , x₀ ]) ∙⊙∼ K₂-map-idf {{Loop2Grp x₀}})) z)
(loop (x₀ == x₀) x)
  ==
hmtpy-nat-∙' (λ x₁ → idp) (loop (x₀ == x₀) x)
-}

      ap-∘ (idf X) (K₂-rec-x₀ x₀ x₀) (loop (x₀ == x₀) x) ◃∙
      ap (ap (idf X)) (K₂-rec-hom-β-pts x₀ (Loop2Grp-map-idf ⊙[ X , x₀ ]) x) ◃∙
      ! (K₂-rec-hom-β-pts x₀ (Loop2Grp-map-idf ⊙[ X , x₀ ]) (ap (idf X) x)) ◃∙
      ! (ap (ap (K₂-rec-y₀ x₀ x₀)) (K₂-map-β-pts (Loop2Grp-map-str (idf X , idp)) x)) ◃∙
      ! (ap-∘ (K₂-rec-y₀ x₀ x₀) (K₂-map (Loop2Grp-map-str (idf X , idp))) (loop (x₀ == x₀) x)) ◃∎


-- ap (fst (K₂-rec-hom x₀ idf2G))
        K₂-map-β-pts (Loop2Grp-map-str (idf X , idp)) x ◃∙
        ap (loop (x₀ == x₀)) (ap-idf x) ◃∙
        ! (K₂-map-β-pts (Loop2Grp-map-idf ⊙[ X , x₀ ]) x) ◃∙
        K₂-map-β-pts (Loop2Grp-map-idf ⊙[ X , x₀ ]) x ∙ ! (ap-idf (loop (x₀ == x₀) x)) ◃∎
