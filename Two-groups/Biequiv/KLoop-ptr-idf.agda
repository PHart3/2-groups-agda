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

  open import KLoop-ptr-idf-aux2 x₀

  abstract
    KLoop-idf :
      ⊙∘-lunit (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∙⊙∼
      ⊙∘-pre (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) (⊙∼-id (⊙idf ⊙[ X , x₀ ])) ∙⊙∼
      sq-KΩ x₀ x₀ (⊙idf ⊙[ X , x₀ ]) ∙⊙∼
      ⊙∘-post (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))
        (apK₂ (Loop2Grp-map-idf ⊙[ X , x₀ ]) ∙⊙∼ K₂-map-idf {{Loop2Grp x₀}})
        ⊙→∼
      ⊙∘-runit (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))
    fst KLoop-idf = K₂-∼∼-ind idp KLoop-ptr-idf-coher
    snd KLoop-idf = idp
