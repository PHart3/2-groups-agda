{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import lib.PathFunctor6
open import lib.types.Pointed
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import LoopK-hom
open import KFunctor-idf
open import SqKLoop
open import apK

module KLoop-ptr-idf-aux1
  {i} {X : Type i} {{ηX : has-level 2 X}} (x₀ : X) (x : x₀ == x₀) where

  open import KLoop-ptr-idf-aux0 x₀ x
  open import KLoop-ptr-idf-defs x₀ x

  abstract
    KLoop-ptr-idf-coher0 :
      hmtpy-nat-∙'
        (λ z →
           fst (sq-KΩ x₀ x₀ (⊙idf ⊙[ X , x₀ ])) z ∙
           ap (fst (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})))
             (fst (apK₂ (Loop2Grp-map-idf ⊙[ X , x₀ ])) z ∙ fst (K₂-map-idf {{Loop2Grp x₀}}) z))
        (loop (x₀ == x₀) x) ◃∎
        =ₛ
      Λ₁
    KLoop-ptr-idf-coher0 = 
      hnat-∙'-∙-ap-∙ (fst (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})))
        (fst (sq-KΩ x₀ x₀ (⊙idf ⊙[ X , x₀ ])))
        (fst (apK₂ (Loop2Grp-map-idf ⊙[ X , x₀ ])))
        (fst (K₂-map-idf {{Loop2Grp x₀}}))
        (loop (x₀ == x₀) x)
        K₂-β-1 K₂-β-2 K₂-β-3
