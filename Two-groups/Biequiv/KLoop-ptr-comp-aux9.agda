{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import SqKLoop
open import LoopK

module KLoop-ptr-comp-aux9 where

  module KLPC-aux9 {i j k} {X : Type i} {Y : Type j} {Z : Type k}
    {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {{ηZ : has-level 2 Z}}
    (f : X → Y) (g : Y → Z) (x₀ : X) (x : x₀ == x₀) where

-- GOAL: Λ₃ =ₛ hmtpy-nat-∙' (λ u → idp) (loop (x₀ == x₀) x) ◃∎

    open import KLoop-ptr-comp-defs f g x₀ x

    private
      s = ap (λ z → ap (fst (K₂-rec-hom z₀ idf2G)) (loop (z₀ == z₀) z)) (ap-∘ g f x)

    abstract
      β-pts-red7 :
        ! (ap (λ q → q) (! (ap (ap (K₂-rec-y₀ x₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g ∘ f , idp)) x)))) ◃∙
        ap (λ z → ap (fst (K₂-rec-hom z₀ idf2G)) (loop (z₀ == z₀) z)) (ap-∘ g f x) ◃∙
        idp ◃∙
        ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (ap (loop (z₀ == z₀)) (ap-∘ g f x))) ◃∙
        ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (K₂-map-β-pts (Loop2Grp-map-str (g ∘ f , idp)) x)) ◃∎
          =ₛ
        idp ◃∎
      β-pts-red7 =
        ! (ap (λ q → q) (! (ap (ap (K₂-rec-y₀ x₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g ∘ f , idp)) x)))) ◃∙
        s ◃∙
        idp ◃∙
        ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (ap (loop (z₀ == z₀)) (ap-∘ g f x))) ◃∙
        ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (K₂-map-β-pts (Loop2Grp-map-str (g ∘ f , idp)) x)) ◃∎
          =ₛ₁⟨ 1 & 1 & ap-∘ (ap (fst (K₂-rec-hom z₀ idf2G))) (loop (z₀ == z₀)) (ap-∘ g f x) ⟩
        ! (ap (λ q → q) (! (ap (ap (K₂-rec-y₀ x₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g ∘ f , idp)) x)))) ◃∙
        ap (ap (fst (K₂-rec-hom z₀ idf2G))) (ap (loop (z₀ == z₀)) (ap-∘ g f x)) ◃∙
        idp ◃∙
        ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (ap (loop (z₀ == z₀)) (ap-∘ g f x))) ◃∙
        ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (K₂-map-β-pts (Loop2Grp-map-str (g ∘ f , idp)) x)) ◃∎
          =ₛ₁⟨ 1 & 3 & !-inv-r (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (ap (loop (z₀ == z₀)) (ap-∘ g f x))) ⟩
        ! (ap (λ q → q) (! (ap (ap (K₂-rec-y₀ x₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g ∘ f , idp)) x)))) ◃∙
        idp ◃∙
        ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (K₂-map-β-pts (Loop2Grp-map-str (g ∘ f , idp)) x)) ◃∎
          =ₛ₁⟨ 0 & 1 &
            ap ! (ap-idf (! (ap (ap (K₂-rec-y₀ x₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g ∘ f , idp)) x)))) ∙
            !-! (ap (ap (K₂-rec-y₀ x₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g ∘ f , idp)) x)) ⟩
        ap (ap (fst (K₂-rec-hom z₀ idf2G))) (K₂-map-β-pts (Loop2Grp-map-str (g ∘ f , idp)) x) ◃∙
        idp ◃∙
        ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (K₂-map-β-pts (Loop2Grp-map-str (g ∘ f , idp)) x)) ◃∎
          =ₛ₁⟨ !-inv-r (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (K₂-map-β-pts (Loop2Grp-map-str (g ∘ f , idp)) x)) ⟩
        idp ◃∎ ∎ₛ
