{-# OPTIONS --without-K --rewriting --lossy-unification --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import LoopK
open import SqKLoop-aux-defs2

module SqKLoop-aux5 where

module _ {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} (x₀ : X) (f : X → Y) where

  private
    y₀ = f x₀
    Λx₀ = wkmag-to-loop x₀ (cohmaghom (idf (x₀ == x₀)) {{idf2G}})
    Λy₀ = wkmag-to-loop y₀ (cohmaghom (idf (y₀ == y₀)) {{idf2G}})

  module Sq-aux5 (c₁ c₂ : base (x₀ == x₀) == base (x₀ == x₀))
    (ζ₃ :
      ap (fst (K₂-rec-hom y₀ idf2G)) (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁)
        ==
      ap f (ap (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₁))
    (ζ₄ :
      ap (fst (K₂-rec-hom y₀ idf2G)) (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₂)
        ==
      ap f (ap (fst (K₂-rec-hom x₀ idf2G)) c₂)) where

    open SqKLoop-abb2 x₀ f c₁ c₂ ζ₃ ζ₄

    SqKLoop-coher4-aux3b =
      ξ₂
        =ₛ⟨ 0 & 1 &
          !-=ₛ
            (ap-seq-∙
              (_∙_ (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀) ∘ K₂-map (Loop2Grp-map-str (f , idp))) c₁))
              (ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₂ ◃∙
              ! ζ₄ ◃∙
              ! (ap-∘ (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)) (K₂-map (Loop2Grp-map-str (f , idp))) c₂) ◃∎)) ⟩
      ξ₃ ∎ₛ

    SqKLoop-coher4-aux3c =
      ξ₃
        =ₛ⟨ 3 & 1 &
          !-=ₛ
            (ap-seq-∙
              (λ u → u ∙ ap (f ∘  K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₂)
              (ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₁ ◃∙
              ! ζ₃ ◃∙
              ! (ap-∘ (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)) (K₂-map (Loop2Grp-map-str (f , idp))) c₁) ◃∎)) ⟩
      ξ₄ ∎ₛ
