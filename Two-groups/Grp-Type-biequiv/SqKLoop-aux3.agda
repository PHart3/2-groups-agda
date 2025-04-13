{-# OPTIONS --without-K --rewriting --lossy-unification --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import 2Semigroup
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import LoopK-hom
open import SqKLoop-aux-defs1

module SqKLoop-aux3 where

module _ {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} (x₀ : X)
  (f : X → Y) (x y : x₀ == x₀) where

  private
    y₀ = f x₀
    Λx₀ = wksgrp-to-loop x₀ (cohsgrphom (idf (x₀ == x₀)) {{idf2G}})
    Λy₀ = wksgrp-to-loop y₀ (cohsgrphom (idf (y₀ == y₀)) {{idf2G}})

  open SqKLoop-abb1 x₀ f x y
  
  SqKLoop-coher3-aux : {b : X} (p : x₀ == b) (q : b == x₀) →
    ! (ap (λ z → ap (fst (K₂-rec-hom y₀ idf2G)) (loop (y₀ == y₀) z)) (ap-∙ f p q)) ◃∙
    ! (ap (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
        (ap (loop (y₀ == y₀)) (∙-ap f p q))) ◃∎
      =ₛ
    idp ◃∎
  SqKLoop-coher3-aux idp q = =ₛ-in idp

  SqKLoop-coher3 =
    δ₂
      =ₛ⟨ 2 & 1 & apCommSq2◃ (ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀))) (loop-comp (x₀ == x₀) x y) ⟩
    _
      =ₛ⟨ 18 & 1 & apCommSq2◃! (ap-∘ (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)) (K₂-map (Loop2Grp-map-str (f , idp)))) (loop-comp (x₀ == x₀) x y) ⟩
    _
      =ₛ⟨ 12 & 2 & SqKLoop-coher3-aux x y ⟩
    δ₃ ∎ₛ
