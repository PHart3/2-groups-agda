{-# OPTIONS --without-K --rewriting --lossy-unification --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import LoopK-hom
open import SqKLoop-aux-defs2
open import SqKLoop-aux6

module SqKLoop-aux7 where

module _ {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} (x₀ : X) (f : X → Y) where

  open Sq-aux6 x₀ f

  module Sq-aux7 (c₁ c₂ : base (x₀ == x₀) == base (x₀ == x₀)) where

    open Sq-aux6-red c₁ c₂

    module _
      (ζ₃ :
        ap (fst (K₂-rec-hom y₀ idf2G)) (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁)
          ==
        ap f (ap (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₁))
      (ζ₄ :
        ap (fst (K₂-rec-hom y₀ idf2G)) (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₂)
          ==
        ap f (ap (fst (K₂-rec-hom x₀ idf2G)) c₂)) where

      open SqKLoop-abb2 x₀ f c₁ c₂ ζ₃ ζ₄

      private
        ξ₅ = 
          ap (λ q → ap (fst (K₂-rec-hom y₀ idf2G)) (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁) ∙ q) (ζ₃-free c₂) ◃∙
          ! (ap (_∙_ (ap (fst (K₂-rec-hom y₀ idf2G)) (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁))) ζ₄) ◃∙
          ! (! (∙-ap (fst (K₂-rec-hom y₀ idf2G))
            (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁) (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₂) ∙ idp)) ◃∙
          ! (ap (ap K₂-rec-y₀)
            (! (∙-ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁ c₂))) ◃∙
          ! (ap-∘ K₂-rec-y₀ (K₂-map (Loop2Grp-map-str (f , idp))) (c₁ ∙ c₂)) ◃∙
          idp ◃∎
        ξ₅' = 
          h₁ ◃∙
          h₂ ◃∙
          h₃ ◃∙
          ! (ap (λ u → u ∙ ap (f ∘  K₂-rec-x₀) c₂)
               (! (ap-∘ K₂-rec-y₀ (K₂-map (Loop2Grp-map-str (f , idp))) c₁))) ◃∙
          ξ₅
          
      ξ₆ =
        ! (ap (_∙_
            (ap K₂-rec-y₀-∘ c₁))
          (! (ap-∘ K₂-rec-y₀ (K₂-map (Loop2Grp-map-str (f , idp))) c₂))) ◃∙
        ap (λ q → q ∙ ap (fst (K₂-rec-hom y₀ idf2G)) (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₂)) (ζ₄-free c₁) ◃∙
        ! (! (∙-ap (fst (K₂-rec-hom y₀ idf2G))
          (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁) (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₂) ∙ idp)) ◃∙
        ! (ap (ap K₂-rec-y₀)
          (! (∙-ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁ c₂))) ◃∙
        ! (ap-∘ K₂-rec-y₀ (K₂-map (Loop2Grp-map-str (f , idp))) (c₁ ∙ c₂)) ◃∙
        idp ◃∎

      SqKLoop-coher4-aux3d =
        ξ₄
          =ₛ⟨ 4 & 7 & ζ₃-red ζ₃ ⟩
        ξ₅' ∎ₛ

      SqKLoop-coher4-aux3e =
        ξ₅'
          =ₛ⟨ 1 & 5 & ζ₄-red ζ₄ ⟩
        ξ₆ ∎ₛ
