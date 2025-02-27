{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import lib.types.LoopSpace
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import SqKLoop
open import LoopK

module KLoop-ptr-comp-aux3 where

  module KLPC-aux3 {i j k} {X : Type i} {Y : Type j} {Z : Type k}
    {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {{ηZ : has-level 2 Z}}
    (f : X → Y) (g : Y → Z) (x₀ : X) (x : x₀ == x₀) where

-- GOAL: Λ₃ =ₛ hmtpy-nat-∙' (λ u → idp) (loop (x₀ == x₀) x) ◃∎

    open import KLoop-ptr-comp-defs f g x₀ x

    -- red-step1
    β-pts-free1 : 
      ap (ap g) (! (ap (ap (K₂-rec-y₀ x₀ y₀)) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x))) ◃∙
      ap (ap g) (! (ap-∘ (K₂-rec-y₀ x₀ y₀) (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) x))) ◃∙
      ap (λ q → q) (ap (λ q → q) (∘-ap g (λ z → fst (K₂-rec-hom y₀ idf2G ⊙∘ K₂-map⊙ (Loop2Grp-map-str (f , idp))) z) (loop (x₀ == x₀) x))) ◃∙
      ap (λ q → q) (ap-∘ (fst ((g , idp) ⊙∘ K₂-rec-hom y₀ idf2G)) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp)))) (loop (x₀ == x₀) x)) ◃∙
      ap (λ q → q) (ap (ap (fst ((g , idp) ⊙∘ K₂-rec-hom y₀ idf2G))) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x)) ◃∎
        =ₛ
      {!!}
    β-pts-free1 = {!!}


    -- red-step3
    β-pts-free3 : 
      ap (λ q → q) (! (ap (ap (λ z → fst (K₂-rec-hom z₀ idf2G ⊙∘ K₂-map⊙ (Loop2Grp-map-str (g , idp))) z)) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x))) ◃∙
      ap (λ q → q)
        (ap (λ q → q) (∘-ap (fst (K₂-rec-hom z₀ idf2G ⊙∘ K₂-map⊙ (Loop2Grp-map-str (g , idp)))) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp)))) (loop (x₀ == x₀) x))) ◃∙
      ap (λ q → q)
        (! (ap (λ q → q) (ap (λ q → q) (∘-ap (fst (K₂-rec-hom z₀ idf2G)) (λ z → fst (K₂-map⊙ (Loop2Grp-map-str (g , idp)) ⊙∘ K₂-map⊙ (Loop2Grp-map-str (f , idp))) z)
          (loop (x₀ == x₀) x))))) ◃∙
      ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (∘-ap (K₂-map (Loop2Grp-map-str (g , idp))) (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) x))) ◃∙
      ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (! (ap (ap (K₂-map (Loop2Grp-map-str (g , idp)))) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x)))) ◃∎
        =ₛ
      {!!}
    β-pts-free3 = {!!}

  -- red-step5
    β-pts-free5 : 
      ! (ap (λ q → q) (ap (ap (g ∘ f)) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x))) ◃∙
      ! (ap (λ q → q) (ap-∘ (g ∘ f) (K₂-rec-x₀ x₀ z₀) (loop (x₀ == x₀) x))) ◃∙
      ap (λ q → q) (ap-∘ g (λ z → f (fst (K₂-rec-hom x₀ idf2G) z)) (loop (x₀ == x₀) x)) ◃∙
      ap (ap g) (ap-∘ f (K₂-rec-x₀ x₀ y₀) (loop (x₀ == x₀) x)) ◃∙
      ap (ap g) (ap (ap f) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x)) ◃∎
        =ₛ
      {!!}
    β-pts-free5 = {!!}
