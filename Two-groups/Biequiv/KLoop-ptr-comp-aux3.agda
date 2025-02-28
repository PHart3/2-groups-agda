{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
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

    β-pts-red1-aux : {c₁ c₂ : K₂ (y₀ == y₀) (Loop2Grp y₀)} {p₁ p₂ : c₁ == c₂} (τ : p₁ == p₂)
      →
      ap (ap g) (! (ap (ap (K₂-rec-y₀ x₀ y₀)) τ)) ∙
      ∘-ap g (K₂-rec-y₀ x₀ y₀) p₁ ∙
      ap (λ q → q) (ap (ap (fst ((g , idp) ⊙∘ K₂-rec-hom y₀ idf2G))) τ)
        ==
      ∘-ap g (K₂-rec-y₀ x₀ y₀) p₂
    β-pts-red1-aux {p₁ = idp} idp = idp

    abstract
      β-pts-red1 : 
        ap (ap g) (! (ap (ap (K₂-rec-y₀ x₀ y₀)) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x))) ◃∙
        ap (ap g) (! (ap-∘ (K₂-rec-y₀ x₀ y₀) (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) x))) ◃∙
        ap (λ q → q) (ap (λ q → q) (∘-ap g (λ z → fst (K₂-rec-hom y₀ idf2G ⊙∘ K₂-map⊙ (Loop2Grp-map-str (f , idp))) z) (loop (x₀ == x₀) x))) ◃∙
        ap (λ q → q) (ap-∘ (fst ((g , idp) ⊙∘ K₂-rec-hom y₀ idf2G)) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp)))) (loop (x₀ == x₀) x)) ◃∙
        ap (λ q → q) (ap (ap (fst ((g , idp) ⊙∘ K₂-rec-hom y₀ idf2G))) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x)) ◃∎
          =ₛ
        ∘-ap g (K₂-rec-y₀ x₀ y₀) (loop (y₀ == y₀) (ap f x)) ◃∎
      β-pts-red1 =
        ap (ap g) (! (ap (ap (K₂-rec-y₀ x₀ y₀)) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x))) ◃∙
        ap (ap g) (! (ap-∘ (K₂-rec-y₀ x₀ y₀) (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) x))) ◃∙
        ap (λ q → q) (ap (λ q → q) (∘-ap g (λ z → fst (K₂-rec-hom y₀ idf2G ⊙∘ K₂-map⊙ (Loop2Grp-map-str (f , idp))) z) (loop (x₀ == x₀) x))) ◃∙
        ap (λ q → q) (ap-∘ (fst ((g , idp) ⊙∘ K₂-rec-hom y₀ idf2G)) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp)))) (loop (x₀ == x₀) x)) ◃∙
        ap (λ q → q) (ap (ap (fst ((g , idp) ⊙∘ K₂-rec-hom y₀ idf2G))) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x)) ◃∎
          =ₛ⟨ 1 & 3 & lemma (loop (x₀ == x₀) x) ⟩
        ap (ap g) (! (ap (ap (K₂-rec-y₀ x₀ y₀)) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x))) ◃∙
        ∘-ap g (K₂-rec-y₀ x₀ y₀) (ap (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) x)) ◃∙
        ap (λ q → q) (ap (ap (fst ((g , idp) ⊙∘ K₂-rec-hom y₀ idf2G))) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x)) ◃∎
          =ₛ₁⟨ β-pts-red1-aux (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x) ⟩
        ∘-ap g (K₂-rec-y₀ x₀ y₀) (loop (y₀ == y₀) (ap f x)) ◃∎ ∎ₛ
          where
            lemma : {b : _} (p : base (x₀ == x₀) == b) →
              ap (ap g) (! (ap-∘ (K₂-rec-y₀ x₀ y₀) (K₂-map (Loop2Grp-map-str (f , idp))) p)) ◃∙
              ap (λ q → q) (ap (λ q → q) (∘-ap g (λ z → fst (K₂-rec-hom y₀ idf2G ⊙∘ K₂-map⊙ (Loop2Grp-map-str (f , idp))) z) p)) ◃∙
              ap (λ q → q) (ap-∘ (fst ((g , idp) ⊙∘ K₂-rec-hom y₀ idf2G)) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp)))) p) ◃∎
                =ₛ
              ∘-ap g (K₂-rec-y₀ x₀ y₀) (ap (K₂-map (Loop2Grp-map-str (f , idp))) p) ◃∎
            lemma idp = =ₛ-in idp
