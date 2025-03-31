{-# OPTIONS --without-K --rewriting --lossy-unification --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import LoopK-hom
open import SqKLoop-aux1
open import SqKLoop-aux2
open import SqKLoop-aux3
open import SqKLoop-aux9

module SqKLoop-aux10 where

module Sq-aux10 {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} (x₀ : X) (f : X → Y) where

  private
    y₀ = f x₀
    Λx₀ = wkmag-to-loop x₀ (cohmaghom (idf (x₀ == x₀)) {{idf2G}})
    Λy₀ = wkmag-to-loop y₀ (cohmaghom (idf (y₀ == y₀)) {{idf2G}})

  module _ (x y : x₀ == x₀) where
   
    η₁ = 
      ∙-ap (f ∘ K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀))
        (loop (x₀ == x₀) x) (loop (x₀ == x₀) y) ◃∙
      ap (ap (f ∘ K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)))
        (loop-comp (x₀ == x₀) x y) ◃∙
      (ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀))
        (loop (x₀ == x₀) (x ∙ y)) ∙
      ap (ap f) (K₂-rec-hom-β-pts x₀ idf2G (x ∙ y)) ∙
      ! (K₂-rec-hom-β-pts y₀ idf2G (ap f (x ∙ y))) ∙
      ! (ap (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
          (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) (x ∙ y))) ∙
      ! (ap-∘ (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)) (K₂-map (Loop2Grp-map-str (f , idp)))
          (loop (x₀ == x₀) (x ∙ y)))) ◃∎

    η₂ =
      ap2 _∙_
        (ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀))
          (loop (x₀ == x₀) x) ∙
        ap (ap f) (K₂-rec-hom-β-pts x₀ idf2G x) ∙
        ! (K₂-rec-hom-β-pts y₀ idf2G (ap f x)) ∙
        ! (ap (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
             (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x)) ∙
        ! (ap-∘
            (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀))
            (K₂-map (Loop2Grp-map-str (f , idp)))
            (loop (x₀ == x₀) x)))
        (ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀))
          (loop (x₀ == x₀) y) ∙
        ap (ap f) (K₂-rec-hom-β-pts x₀ idf2G y) ∙
        ! (K₂-rec-hom-β-pts y₀ idf2G (ap f y)) ∙
        ! (ap (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
            (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) y)) ∙
        ! (ap-∘
            (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀))
            (K₂-map (Loop2Grp-map-str (f , idp)))
            (loop (x₀ == x₀) y))) ◃∙
      ∙-assoc2-!-inv-l
        (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀) ∘ K₂-map (Loop2Grp-map-str (f , idp)))
        idp idp (loop (x₀ == x₀) x) (loop (x₀ == x₀) y) ◃∙
      ap (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀) ∘ K₂-map (Loop2Grp-map-str (f , idp))))
        (loop-comp (x₀ == x₀) x y) ◃∎

    private
      Σ₁ = SqKLoop-coher1 x₀ f x y
      Σ₂ = SqKLoop-coher2 x₀ f x y
      Σ₃ = SqKLoop-coher3 x₀ f x y
      Σ₄ = SqKLoop-coher4 x₀ f x y

    abstract
      SqKLoop-coher :
        η₁
          =ₛ
        η₂
      SqKLoop-coher = Σ₁ ∙ₛ Σ₂ ∙ₛ Σ₃ ∙ₛ Σ₄
