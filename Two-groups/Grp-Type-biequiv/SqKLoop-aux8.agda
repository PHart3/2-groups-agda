{-# OPTIONS --without-K --rewriting --lossy-unification --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import LoopK-hom
open import SqKLoop-aux6

module SqKLoop-aux8 where

module Sq-aux8 {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} (x₀ : X) (f : X → Y) where

  open Sq-aux6 x₀ f

  φ = K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀) ∘ K₂-map (Loop2Grp-map-str (f , idp))

  abstract
    SqKLoop-coher4-aux3f : {b : _} (c₁ : b == base (x₀ == x₀)) (c₂ : base (x₀ == x₀) == b) →
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
        =ₛ
      ∙-assoc2-!-inv-l φ idp idp c₁ c₂ ◃∙
      idp ◃∎
    SqKLoop-coher4-aux3f idp c₂ = =ₛ-in (lemma c₂)
      where
        lemma : {b : _} (c : base (x₀ == x₀) == b) →
          ! (ap (λ q → q)(! (ap-∘ K₂-rec-y₀ (K₂-map (Loop2Grp-map-str (f , idp))) c))) ∙
          ! (ap-∘ K₂-rec-y₀ (K₂-map (Loop2Grp-map-str (f , idp))) c) ∙ idp
            ==
          ∙-assoc2-!-inv-l-aux φ c idp idp idp ∙ idp
        lemma idp = idp
