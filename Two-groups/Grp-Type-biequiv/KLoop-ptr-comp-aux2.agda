{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import 2Grp
open import 2Magma
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import SqKLoop
open import LoopK
open import KLoop-ptr-comp-aux0

module KLoop-ptr-comp-aux2 where

module KLPC-aux2 {i j k} {X : Type i} {Y : Type j} {Z : Type k}
  {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {{ηZ : has-level 2 Z}}
  (f : X → Y) (g : Y → Z) (x₀ : X) (x : x₀ == x₀) where

  open import KLoop-ptr-comp-defs f g x₀ x
  open import KLoop-ptr-comp-defs2 f g x₀ x
  open import KLoop-ptr-comp-defs3 f g x₀ x

  open KLPC-aux0 f g x₀ x

  abstract
    K₂-β-3-β-pts :
      hmtpy-nat-∙' (fst (sq-KΩ y₀ z₀ (g , idp))) (ap (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp)))) (loop (x₀ == x₀) x)) ◃∎
        =ₛ
      ap (ap (λ z → fst ((g , idp) ⊙∘ K₂-rec-hom y₀ idf2G) z)) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x) ◃∙
      ap-∘ g (K₂-rec-x₀ y₀ z₀) (loop (y₀ == y₀) (ap f x)) ◃∙
      ap (ap g) (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f x)) ◃∙
      ! (K₂-rec-hom-β-pts z₀ (idf2G {{Loop2Grp z₀}}) (ap g (ap f x))) ◃∙
      ! (ap (ap (K₂-rec-y₀ y₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g , idp)) (ap f x))) ◃∙
      ! (ap-∘ (K₂-rec-y₀ y₀ z₀) (K₂-map (Loop2Grp-map-str (g , idp))) (loop (y₀ == y₀) (ap f x))) ◃∙
      ! (ap (ap (λ z → fst (K₂-rec-hom z₀ idf2G ⊙∘ K₂-map⊙ (Loop2Grp-map-str (g , idp))) z)) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x)) ◃∎
    K₂-β-3-β-pts =
      hmtpy-nat-∙' (fst (sq-KΩ y₀ z₀ (g , idp))) (ap (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp)))) (loop (x₀ == x₀) x)) ◃∎
        =ₛ⟨ apCommSq2◃' (λ (p : base (y₀ == y₀) == base (y₀ == y₀)) → hmtpy-nat-∙' (fst (sq-KΩ y₀ z₀ (g , idp))) p) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x) ⟩
      ap (ap (fst ((g , idp) ⊙∘ K₂-rec-hom y₀ idf2G))) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x) ◃∙
      hmtpy-nat-∙' (fst (sq-KΩ y₀ z₀ (g , idp))) (loop (y₀ == y₀) (ap f x)) ◃∙
      ! (ap (ap (λ z → fst (K₂-rec-hom z₀ idf2G ⊙∘ K₂-map⊙ (Loop2Grp-map-str (g , idp))) z)) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x)) ◃∎
        =ₛ⟨ 1 & 1 & K₂-β-3 ⟩
      ap (ap (fst ((g , idp) ⊙∘ K₂-rec-hom y₀ idf2G))) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x) ◃∙
      ap-∘ g (K₂-rec-x₀ y₀ z₀) (loop (y₀ == y₀) (ap f x)) ◃∙
      ap (ap g) (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f x)) ◃∙
      ! (K₂-rec-hom-β-pts z₀ (idf2G {{Loop2Grp z₀}}) (ap g (ap f x))) ◃∙
      ! (ap (ap (K₂-rec-y₀ y₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g , idp)) (ap f x))) ◃∙
      ! (ap-∘ (K₂-rec-y₀ y₀ z₀) (K₂-map (Loop2Grp-map-str (g , idp))) (loop (y₀ == y₀) (ap f x))) ◃∙
      ! (ap (ap (λ z → fst (K₂-rec-hom z₀ idf2G ⊙∘ K₂-map⊙ (Loop2Grp-map-str (g , idp))) z)) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x)) ◃∎ ∎ₛ

  private
    abstract
      τ :
        ap (λ q → q) (hmtpy-nat-∙' (λ u → fst (sq-KΩ y₀ z₀ (g , idp)) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp))) u)) (loop (x₀ == x₀) x)) ◃∎
          =ₛ
        ap (λ q → q) (ap-∘ (fst ((g , idp) ⊙∘ K₂-rec-hom y₀ idf2G)) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp)))) (loop (x₀ == x₀) x)) ◃∙
        ap (λ q → q) (ap (ap (fst ((g , idp) ⊙∘ K₂-rec-hom y₀ idf2G))) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x)) ◃∙
        ap (λ q → q) (ap-∘ g (K₂-rec-x₀ y₀ z₀) (loop (y₀ == y₀) (ap f x))) ◃∙
        ap (λ q → q) (ap (ap g) (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f x))) ◃∙
        ap (λ q → q) (! (K₂-rec-hom-β-pts z₀ (idf2G {{Loop2Grp z₀}}) (ap g (ap f x)))) ◃∙
        ap (λ q → q) (! (ap (ap (K₂-rec-y₀ y₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g , idp)) (ap f x)))) ◃∙
        ap (λ q → q) (! (ap-∘ (K₂-rec-y₀ y₀ z₀) (K₂-map (Loop2Grp-map-str (g , idp))) (loop (y₀ == y₀) (ap f x)))) ◃∙
        ap (λ q → q) (! (ap (ap (λ z → fst (K₂-rec-hom z₀ idf2G ⊙∘ K₂-map⊙ (Loop2Grp-map-str (g , idp))) z)) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x))) ◃∙
        ap (λ q → q) (ap (λ q → q) (∘-ap (fst (K₂-rec-hom z₀ idf2G ⊙∘ K₂-map⊙ (Loop2Grp-map-str (g , idp)))) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp)))) (loop (x₀ == x₀) x))) ◃∎
      τ =
        ap (λ q → q) (hmtpy-nat-∙' (λ u → fst (sq-KΩ y₀ z₀ (g , idp)) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp))) u)) (loop (x₀ == x₀) x)) ◃∎
          =ₛ⟨ ap-seq-=ₛ (λ q → q) ρ₂ ⟩
        _
          =ₛ⟨ 1 & 1 & ap-seq-=ₛ (λ q → q) K₂-β-3-β-pts ⟩
        ap (λ q → q) (ap-∘ (fst ((g , idp) ⊙∘ K₂-rec-hom y₀ idf2G)) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp)))) (loop (x₀ == x₀) x)) ◃∙
        ap (λ q → q) (ap (ap (fst ((g , idp) ⊙∘ K₂-rec-hom y₀ idf2G))) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x)) ◃∙
        ap (λ q → q) (ap-∘ g (K₂-rec-x₀ y₀ z₀) (loop (y₀ == y₀) (ap f x))) ◃∙
        ap (λ q → q) (ap (ap g) (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f x))) ◃∙
        ap (λ q → q) (! (K₂-rec-hom-β-pts z₀ (idf2G {{Loop2Grp z₀}}) (ap g (ap f x)))) ◃∙
        ap (λ q → q) (! (ap (ap (K₂-rec-y₀ y₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g , idp)) (ap f x)))) ◃∙
        ap (λ q → q) (! (ap-∘ (K₂-rec-y₀ y₀ z₀) (K₂-map (Loop2Grp-map-str (g , idp))) (loop (y₀ == y₀) (ap f x)))) ◃∙
        ap (λ q → q) (! (ap (ap (λ z → fst (K₂-rec-hom z₀ idf2G ⊙∘ K₂-map⊙ (Loop2Grp-map-str (g , idp))) z)) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x))) ◃∙
        ap (λ q → q) (ap (λ q → q) (∘-ap (fst (K₂-rec-hom z₀ idf2G ⊙∘ K₂-map⊙ (Loop2Grp-map-str (g , idp)))) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp)))) (loop (x₀ == x₀) x))) ◃∎ ∎ₛ

  abstract
    KLoop-∘-coher1 : Λ₁ =ₛ Λ₃
    KLoop-∘-coher1 =
      Λ₁
        =ₛ⟨ 14 & 1 & τ ⟩
      Λ₂
        =ₛ₁⟨ 30 & 2 &
          ap-!-!-inv
            (ap (fst (K₂-rec-hom z₀ idf2G)))
            (K₂-map-β-pts (cohmaghom (ap g) {{Loop2Grp-map-str (g , idp)}} ∘2Mσ cohmaghom (ap f) {{Loop2Grp-map-str (f , idp)}}) x) ⟩
      Λ₃ ∎ₛ
