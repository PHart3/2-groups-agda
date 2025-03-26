{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import SqKLoop
open import LoopK-hom

module KLoop-ptr-comp-aux4 where

module KLPC-aux4 {i j k} {X : Type i} {Y : Type j} {Z : Type k}
  {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {{ηZ : has-level 2 Z}}
  (f : X → Y) (g : Y → Z) (x₀ : X) (x : x₀ == x₀) where

  open import KLoop-ptr-comp-defs f g x₀ x

  β-pts-red3a-aux : {b : K₂ (x₀ == x₀) (Loop2Grp x₀)} (p : base (x₀ == x₀) == b) →
    ap (λ q → q)
      (ap (λ q → q) (∘-ap (fst (K₂-rec-hom z₀ idf2G ⊙∘ K₂-map⊙ (Loop2Grp-map-str (g , idp)))) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp)))) p)) ◃∙
    ap (λ q → q)
      (! (ap (λ q → q) (ap (λ q → q) (∘-ap (fst (K₂-rec-hom z₀ idf2G)) (λ z → fst (K₂-map⊙ (Loop2Grp-map-str (g , idp)) ⊙∘ K₂-map⊙ (Loop2Grp-map-str (f , idp))) z) p)))) ◃∙
    ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (∘-ap (K₂-map (Loop2Grp-map-str (g , idp))) (K₂-map (Loop2Grp-map-str (f , idp))) p)) ◃∎
      =ₛ
    ap-∘ (fst (K₂-rec-hom z₀ idf2G)) (K₂-map (Loop2Grp-map-str (g , idp))) (ap (K₂-map (Loop2Grp-map-str (f , idp))) p) ◃∎
  β-pts-red3a-aux idp = =ₛ-in idp

  private
    μ₁ =
      ap (λ q → q) (! (ap (ap (λ z → fst (K₂-rec-hom z₀ idf2G ⊙∘ K₂-map⊙ (Loop2Grp-map-str (g , idp))) z)) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x))) ◃∙
      ap (λ q → q)
        (ap (λ q → q) (∘-ap (fst (K₂-rec-hom z₀ idf2G ⊙∘ K₂-map⊙ (Loop2Grp-map-str (g , idp)))) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp)))) (loop (x₀ == x₀) x))) ◃∙
      ap (λ q → q)
        (! (ap (λ q → q) (ap (λ q → q) (∘-ap (fst (K₂-rec-hom z₀ idf2G)) (λ z → fst (K₂-map⊙ (Loop2Grp-map-str (g , idp)) ⊙∘ K₂-map⊙ (Loop2Grp-map-str (f , idp))) z)
          (loop (x₀ == x₀) x))))) ◃∙
      ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (∘-ap (K₂-map (Loop2Grp-map-str (g , idp))) (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) x))) ◃∙
      ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (! (ap (ap (K₂-map (Loop2Grp-map-str (g , idp)))) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x)))) ◃∎
    μ₂ =
      ap (λ q → q) (! (ap (ap (λ z → fst (K₂-rec-hom z₀ idf2G ⊙∘ K₂-map⊙ (Loop2Grp-map-str (g , idp))) z)) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x))) ◃∙
      ap-∘ (fst (K₂-rec-hom z₀ idf2G)) (K₂-map (Loop2Grp-map-str (g , idp))) (ap (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) x)) ◃∙
      ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (! (ap (ap (K₂-map (Loop2Grp-map-str (g , idp)))) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x)))) ◃∎

  β-pts-red3a = 
    μ₁
      =ₛ⟨ 1 & 3 & β-pts-red3a-aux (loop (x₀ == x₀) x) ⟩
    μ₂ ∎ₛ

  β-pts-red3b-aux : {c₁ c₂ : K₂ (y₀ == y₀) (Loop2Grp y₀)} {p₁ p₂ : c₁ == c₂} (τ : p₁ == p₂)
    →
    ap (λ q → q) (! (ap (ap (λ z → fst (K₂-rec-hom z₀ idf2G ⊙∘ K₂-map⊙ (Loop2Grp-map-str (g , idp))) z)) τ)) ◃∙
    ap-∘ (fst (K₂-rec-hom z₀ idf2G)) (K₂-map (Loop2Grp-map-str (g , idp))) p₁ ◃∙
    ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (! (ap (ap (K₂-map (Loop2Grp-map-str (g , idp)))) τ))) ◃∎
      =ₛ
    ap-∘ (fst (K₂-rec-hom z₀ idf2G)) (K₂-map (Loop2Grp-map-str (g , idp))) p₂ ◃∎
  β-pts-red3b-aux {p₁ = idp} idp = =ₛ-in idp

  β-pts-red3b = 
    μ₂
      =ₛ⟨ β-pts-red3b-aux (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x) ⟩
    ap-∘ (fst (K₂-rec-hom z₀ idf2G)) (K₂-map (Loop2Grp-map-str (g , idp))) (loop (y₀ == y₀) (ap f x)) ◃∎ ∎ₛ

  abstract
    β-pts-red3 : 
      ap (λ q → q) (! (ap (ap (λ z → fst (K₂-rec-hom z₀ idf2G ⊙∘ K₂-map⊙ (Loop2Grp-map-str (g , idp))) z)) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x))) ◃∙
      ap (λ q → q)
        (ap (λ q → q) (∘-ap (fst (K₂-rec-hom z₀ idf2G ⊙∘ K₂-map⊙ (Loop2Grp-map-str (g , idp)))) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp)))) (loop (x₀ == x₀) x))) ◃∙
      ap (λ q → q)
        (! (ap (λ q → q) (ap (λ q → q) (∘-ap (fst (K₂-rec-hom z₀ idf2G)) (λ z → fst (K₂-map⊙ (Loop2Grp-map-str (g , idp)) ⊙∘ K₂-map⊙ (Loop2Grp-map-str (f , idp))) z)
          (loop (x₀ == x₀) x))))) ◃∙
      ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (∘-ap (K₂-map (Loop2Grp-map-str (g , idp))) (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) x))) ◃∙
      ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (! (ap (ap (K₂-map (Loop2Grp-map-str (g , idp)))) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x)))) ◃∎
        =ₛ
      ap-∘ (fst (K₂-rec-hom z₀ idf2G)) (K₂-map (Loop2Grp-map-str (g , idp))) (loop (y₀ == y₀) (ap f x)) ◃∎
    β-pts-red3 = β-pts-red3a ∙ₛ β-pts-red3b
