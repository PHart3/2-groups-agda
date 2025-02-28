{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import SqKLoop
open import LoopK

module KLoop-ptr-comp-aux8 where

  module KLPC-aux8 {i j k} {X : Type i} {Y : Type j} {Z : Type k}
    {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {{ηZ : has-level 2 Z}}
    (f : X → Y) (g : Y → Z) (x₀ : X) (x : x₀ == x₀) where

-- GOAL: Λ₃ =ₛ hmtpy-nat-∙' (λ u → idp) (loop (x₀ == x₀) x) ◃∎

    open import KLoop-ptr-comp-defs f g x₀ x

    abstract
      β-pts-red6 :
        ! (ap (λ q → q) (! (K₂-rec-hom-β-pts z₀ (idf2G {{Loop2Grp z₀}}) (ap (g ∘ f) x)))) ◃∙
        ap-∘ g f x ◃∙
        idp ◃∙
        ap (λ q → q) (! (K₂-rec-hom-β-pts z₀ (idf2G {{Loop2Grp z₀}}) (ap g (ap f x)))) ◃∎
          =ₛ
        ap (λ z → ap (fst (K₂-rec-hom z₀ idf2G)) (loop (z₀ == z₀) z)) (ap-∘ g f x) ◃∎
      β-pts-red6 =
        ! (ap (λ q → q) (! (K₂-rec-hom-β-pts z₀ (idf2G {{Loop2Grp z₀}}) (ap (g ∘ f) x)))) ◃∙
        ap-∘ g f x ◃∙
        idp ◃∙
        ap (λ q → q) (! (K₂-rec-hom-β-pts z₀ (idf2G {{Loop2Grp z₀}}) (ap g (ap f x)))) ◃∎
          =ₛ₁⟨ 2 & 2 & ap-idf (! (K₂-rec-hom-β-pts z₀ (idf2G {{Loop2Grp z₀}}) (ap g (ap f x)))) ⟩
        ! (ap (λ q → q) (! (K₂-rec-hom-β-pts z₀ (idf2G {{Loop2Grp z₀}}) (ap (g ∘ f) x)))) ◃∙
        ap-∘ g f x ◃∙
        ! (K₂-rec-hom-β-pts z₀ idf2G (ap g (ap f x))) ◃∎
          =ₛ₁⟨ 1 & 1 & ! (ap-idf (ap-∘ g f x)) ⟩
        ! (ap (λ q → q) (! (K₂-rec-hom-β-pts z₀ (idf2G {{Loop2Grp z₀}}) (ap (g ∘ f) x)))) ◃∙
        ap (λ z → z) (ap-∘ g f x) ◃∙
        ! (K₂-rec-hom-β-pts z₀ idf2G (ap g (ap f x))) ◃∎
          =ₛ₁⟨ 0 & 1 & ap ! (ap-idf (! (K₂-rec-hom-β-pts z₀ idf2G (ap (g ∘ f) x)))) ∙ !-! (K₂-rec-hom-β-pts z₀ idf2G (ap (g ∘ f) x)) ⟩
        K₂-rec-hom-β-pts z₀ idf2G (ap (g ∘ f) x) ◃∙
        ap (λ z → z) (ap-∘ g f x) ◃∙
        ! (K₂-rec-hom-β-pts z₀ idf2G (ap g (ap f x))) ◃∎
          =ₛ⟨ !ₛ (hmtpy-nat-∙◃  (K₂-rec-hom-β-pts z₀ (idf2G {{Loop2Grp z₀}})) (ap-∘ g f x)) ⟩
        ap (λ z → ap (fst (K₂-rec-hom z₀ idf2G)) (loop (z₀ == z₀) z)) (ap-∘ g f x) ◃∎ ∎ₛ
