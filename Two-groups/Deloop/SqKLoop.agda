{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import K-hom-ind
open import KFunctor
open import Delooping
open import LoopK
open import SqKLoop-aux10

module SqKLoop where

module _ {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} (x₀ : X) (y₀ : Y) where

  private  
    Λx₀ = wkmag-to-loop x₀ (cohmaghom (idf (x₀ == x₀)) {{idf2G}})
    Λy₀ = wkmag-to-loop y₀ (cohmaghom (idf (y₀ == y₀)) {{idf2G}})
    K₂-rec-x₀ = K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)
    K₂-rec-y₀ = K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)

  open Sq-aux10 x₀

  sq-KΩ : (f* : ⊙[ X , x₀ ] ⊙→ ⊙[ Y , y₀ ]) →
    f* ⊙∘ K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})
      ⊙-comp
    K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}) ⊙∘ (K₂-map (Loop2Grp-map-str f*) , idp)
  fst (sq-KΩ (f , idp)) =
    K₂-∼-ind
      (f ∘ K₂-rec-x₀)
      (K₂-rec-y₀ ∘ K₂-map (Loop2Grp-map-str (f , idp)))
      idp
      (λ x →
        ap-∘ f K₂-rec-x₀ (loop (x₀ == x₀) x) ∙
        ap (ap f) (K₂-rec-hom-β-pts x₀ idf2G x) ∙
        ! (K₂-rec-hom-β-pts y₀ idf2G (ap f x)) ∙
        ! (ap (ap K₂-rec-y₀) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x)) ∙
        ! (ap-∘ K₂-rec-y₀ (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) x)))
      (SqKLoop-coher f)
  snd (sq-KΩ (f , idp)) = idp
