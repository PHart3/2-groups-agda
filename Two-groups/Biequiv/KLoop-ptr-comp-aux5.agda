{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import SqKLoop
open import LoopK

module KLoop-ptr-comp-aux5 where

  module KLPC-aux5 {i j k} {X : Type i} {Y : Type j} {Z : Type k}
    {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {{ηZ : has-level 2 Z}}
    (f : X → Y) (g : Y → Z) (x₀ : X) (x : x₀ == x₀) where

-- GOAL: Λ₃ =ₛ hmtpy-nat-∙' (λ u → idp) (loop (x₀ == x₀) x) ◃∎

    open import KLoop-ptr-comp-defs f g x₀ x

    -- red-step5
    
    β-pts-red3-aux : {c₁ c₂ : X} {p₁ p₂ : c₁ == c₂} (τ : p₁ == p₂)
      →
      ! (ap (λ q → q) (ap (ap (g ∘ f)) τ)) ◃∙
      ap-∘ g f p₁ ◃∙
      ap (ap g) (ap (ap f) τ) ◃∎
        =ₛ
      ap-∘ g f p₂ ◃∎
    β-pts-red3-aux {p₁ = idp} idp = =ₛ-in idp

    abstract
      β-pts-red5 : 
        ! (ap (λ q → q) (ap (ap (g ∘ f)) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x))) ◃∙
        ! (ap (λ q → q) (ap-∘ (g ∘ f) (K₂-rec-x₀ x₀ z₀) (loop (x₀ == x₀) x))) ◃∙
        ap (λ q → q) (ap-∘ g (λ z → f (fst (K₂-rec-hom x₀ idf2G) z)) (loop (x₀ == x₀) x)) ◃∙
        ap (ap g) (ap-∘ f (K₂-rec-x₀ x₀ y₀) (loop (x₀ == x₀) x)) ◃∙
        ap (ap g) (ap (ap f) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x)) ◃∎
          =ₛ
        ap-∘ g f x ◃∎
      β-pts-red5 =
        ! (ap (λ q → q) (ap (ap (g ∘ f)) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x))) ◃∙
        ! (ap (λ q → q) (ap-∘ (g ∘ f) (K₂-rec-x₀ x₀ z₀) (loop (x₀ == x₀) x))) ◃∙
        ap (λ q → q) (ap-∘ g (λ z → f (fst (K₂-rec-hom x₀ idf2G) z)) (loop (x₀ == x₀) x)) ◃∙
        ap (ap g) (ap-∘ f (K₂-rec-x₀ x₀ y₀) (loop (x₀ == x₀) x)) ◃∙
        ap (ap g) (ap (ap f) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x)) ◃∎
          =ₛ⟨ 1 & 3 & lemma (loop (x₀ == x₀) x) ⟩
        ! (ap (λ q → q) (ap (ap (g ∘ f)) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x))) ◃∙
        ap-∘ g f (ap (K₂-rec-x₀ x₀ z₀) (loop (x₀ == x₀) x)) ◃∙
        ap (ap g) (ap (ap f) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x)) ◃∎
          =ₛ⟨ β-pts-red3-aux (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x) ⟩
        ap-∘ g f x ◃∎ ∎ₛ
          where
            lemma : {b : _} (p : base (x₀ == x₀) == b) →
              ! (ap (λ q → q) (ap-∘ (g ∘ f) (K₂-rec-x₀ x₀ z₀) p)) ◃∙
              ap (λ q → q) (ap-∘ g (λ z → f (fst (K₂-rec-hom x₀ idf2G) z)) p) ◃∙
              ap (ap g) (ap-∘ f (K₂-rec-x₀ x₀ y₀) p) ◃∎
                =ₛ
              ap-∘ g f (ap (K₂-rec-x₀ x₀ z₀) p) ◃∎
            lemma idp = =ₛ-in idp
