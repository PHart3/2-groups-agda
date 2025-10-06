{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import 2Semigroup
open import 2Grp
open import Hmtpy2Grp
open import K-hom-ind
open import KFunctor
open import Delooping
open import LoopK-hom
open import SqKLoop-aux10

module SqKLoop-lossy where

module SqKL-defs {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} (x₀ : X) (y₀ : Y) where

  Λx₀ = wksgrp-to-loop x₀ (cohsgrphom (idf (x₀ == x₀)) {{idf2G}})
  Λy₀ = wksgrp-to-loop y₀ (cohsgrphom (idf (y₀ == y₀)) {{idf2G}})

  K₂-rec-x₀ = K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)
  K₂-rec-y₀ = K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)

module _ {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} (x₀ : X) (y₀ : Y) where

  open SqKL-defs x₀ y₀

  sq-KΩ-lossy : (f* : ⊙[ X , x₀ ] ⊙→ ⊙[ Y , y₀ ]) →
    f* ⊙∘ K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})
      ⊙-crd∼
    K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}) ⊙∘ (K₂-map (Loop2Grp-map-str f*) , idp)
  fst (sq-KΩ-lossy (f , idp)) =
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
      κ
        where
          open Sq-aux10 x₀ f
          abstract
            κ : (x y : x₀ == x₀) → η₁ x y =ₛ η₂ x y
            κ = SqKLoop-coher
  snd (sq-KΩ-lossy (f , idp)) = idp
