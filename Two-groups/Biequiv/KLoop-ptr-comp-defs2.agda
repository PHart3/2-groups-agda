{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import LoopK
open import KFunctor-comp
open import SqKLoop
open import apK
open import KLoop-ptr-comp-aux0

module KLoop-ptr-comp-defs2  {i j k} {X : Type i} {Y : Type j} {Z : Type k}
  {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {{ηZ : has-level 2 Z}}
  (f : X → Y) (g : Y → Z) (x₀ : X) (x : x₀ == x₀) where

  open import KLoop-ptr-comp-defs f g x₀ x

  Λ₀ =
    hmtpy-nat-∙'
      (λ u →
        ! (fst (sq-KΩ x₀ z₀ (g ∘ f , idp)) u) ∙
        ap g (fst (sq-KΩ x₀ y₀ (f , idp)) u) ∙
        fst (sq-KΩ y₀ z₀ (g , idp)) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp))) u) ∙
        ! (ap (fst (K₂-rec-hom z₀ idf2G)) (fst (apK₂ {σ₁ = Loop2Grp-map-str (g ∘ f , idp)} (Loop2Grp-map-∘ (g , idp) (f , idp))) u ∙
          fst (K₂-map-∘ (Loop2Grp-map-str (f , idp)) (Loop2Grp-map-str (g , idp))) u)))
      (loop (x₀ == x₀) x) ◃∎

  Λ₁ =     
    idp ◃∙
    ! (ap (λ q → q) (! (ap-∘ (K₂-rec-y₀ x₀ z₀) (K₂-map (Loop2Grp-map-str (g ∘ f , idp))) (loop (x₀ == x₀) x)))) ◃∙
    ! (ap (λ q → q) (! (ap (ap (K₂-rec-y₀ x₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g ∘ f , idp)) x)))) ◃∙
    ! (ap (λ q → q) (! (K₂-rec-hom-β-pts z₀ (idf2G {{Loop2Grp z₀}}) (ap (g ∘ f) x)))) ◃∙
    ! (ap (λ q → q) (ap (ap (g ∘ f)) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x))) ◃∙
    ! (ap (λ q → q) (ap-∘ (g ∘ f) (K₂-rec-x₀ x₀ z₀) (loop (x₀ == x₀) x))) ◃∙
    ap (λ q → q) (ap-∘ g (λ z → f (fst (K₂-rec-hom x₀ idf2G) z)) (loop (x₀ == x₀) x)) ◃∙
    ap (ap g) (ap-∘ f (K₂-rec-x₀ x₀ y₀) (loop (x₀ == x₀) x)) ◃∙
    ap (ap g) (ap (ap f) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x)) ◃∙
    ap (ap g) (! (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f x))) ◃∙
    ap (ap g) (! (ap (ap (K₂-rec-y₀ x₀ y₀)) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x))) ◃∙
    ap (ap g) (! (ap-∘ (K₂-rec-y₀ x₀ y₀) (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) x))) ◃∙
    idp ◃∙
    ap (λ q → q) (ap (λ q → q) (∘-ap g (λ z → fst (K₂-rec-hom y₀ idf2G ⊙∘ K₂-map⊙ (Loop2Grp-map-str (f , idp))) z) (loop (x₀ == x₀) x))) ◃∙
    ap (λ q → q) (hmtpy-nat-∙' (λ u → fst (sq-KΩ y₀ z₀ (g , idp)) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp))) u)) (loop (x₀ == x₀) x)) ◃∙
    idp ◃∙
    ap (λ q → q)
      (! (ap (λ q → q) (ap (λ q → q) (∘-ap (fst (K₂-rec-hom z₀ idf2G)) (λ z → fst (K₂-map⊙ (Loop2Grp-map-str (g , idp)) ⊙∘ K₂-map⊙ (Loop2Grp-map-str (f , idp))) z)
        (loop (x₀ == x₀) x))))) ◃∙
    idp ◃∙
    idp ◃∙
    ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (∘-ap (K₂-map (Loop2Grp-map-str (g , idp))) (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) x))) ◃∙
    ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (! (ap (ap (K₂-map (Loop2Grp-map-str (g , idp)))) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x)))) ◃∙
    ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (! (K₂-map-β-pts (Loop2Grp-map-str (g , idp)) (ap f x)))) ◃∙
    ! (ap (ap (fst (K₂-rec-hom z₀ idf2G)))
        (K₂-map-β-pts (cohmaghom (ap g) {{Loop2Grp-map-str (g , idp)}} ∘2Mσ cohmaghom (ap f) {{Loop2Grp-map-str (f , idp)}}) x)) ◃∙
    ! (ap
        (ap (fst (K₂-rec-hom z₀ idf2G)))
          (! (K₂-map-β-pts (cohmaghom (ap g) {{Loop2Grp-map-str (g , idp)}} ∘2Mσ cohmaghom (ap f) {{Loop2Grp-map-str (f , idp)}}) x))) ◃∙
    ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (ap (loop (z₀ == z₀)) (ap-∘ g f x))) ◃∙
    ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (K₂-map-β-pts (Loop2Grp-map-str (g ∘ f , idp)) x)) ◃∙
    ap (λ q → q) (! (ap (λ q → q) (ap-∘ (fst (K₂-rec-hom z₀ idf2G)) (λ z → fst (K₂-map⊙ (Loop2Grp-map-str (g ∘ f , idp))) z) (loop (x₀ == x₀) x)))) ◃∙
    idp ◃∙
    idp ◃∙
    idp ◃∎

  Λ₂ =
    idp ◃∙
    ! (ap (λ q → q) (! (ap-∘ (K₂-rec-y₀ x₀ z₀) (K₂-map (Loop2Grp-map-str (g ∘ f , idp))) (loop (x₀ == x₀) x)))) ◃∙
    ! (ap (λ q → q) (! (ap (ap (K₂-rec-y₀ x₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g ∘ f , idp)) x)))) ◃∙
    ! (ap (λ q → q) (! (K₂-rec-hom-β-pts z₀ (idf2G {{Loop2Grp z₀}}) (ap (g ∘ f) x)))) ◃∙
    ! (ap (λ q → q) (ap (ap (g ∘ f)) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x))) ◃∙
    ! (ap (λ q → q) (ap-∘ (g ∘ f) (K₂-rec-x₀ x₀ z₀) (loop (x₀ == x₀) x))) ◃∙
    ap (λ q → q) (ap-∘ g (λ z → f (fst (K₂-rec-hom x₀ idf2G) z)) (loop (x₀ == x₀) x)) ◃∙
    ap (ap g) (ap-∘ f (K₂-rec-x₀ x₀ y₀) (loop (x₀ == x₀) x)) ◃∙
    ap (ap g) (ap (ap f) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x)) ◃∙
    ap (ap g) (! (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f x))) ◃∙
    ap (ap g) (! (ap (ap (K₂-rec-y₀ x₀ y₀)) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x))) ◃∙
    ap (ap g) (! (ap-∘ (K₂-rec-y₀ x₀ y₀) (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) x))) ◃∙
    idp ◃∙
    ap (λ q → q) (ap (λ q → q) (∘-ap g (λ z → fst (K₂-rec-hom y₀ idf2G ⊙∘ K₂-map⊙ (Loop2Grp-map-str (f , idp))) z) (loop (x₀ == x₀) x))) ◃∙
    ap (λ q → q) (ap-∘ (fst ((g , idp) ⊙∘ K₂-rec-hom y₀ idf2G)) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp)))) (loop (x₀ == x₀) x)) ◃∙
    ap (λ q → q) (ap (ap (fst ((g , idp) ⊙∘ K₂-rec-hom y₀ idf2G))) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x)) ◃∙
    ap (λ q → q) (ap-∘ g (K₂-rec-x₀ y₀ z₀) (loop (y₀ == y₀) (ap f x))) ◃∙
    ap (λ q → q) (ap (ap g) (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f x))) ◃∙
    ap (λ q → q) (! (K₂-rec-hom-β-pts z₀ (idf2G {{Loop2Grp z₀}}) (ap g (ap f x)))) ◃∙
    ap (λ q → q) (! (ap (ap (K₂-rec-y₀ y₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g , idp)) (ap f x)))) ◃∙
    ap (λ q → q) (! (ap-∘ (K₂-rec-y₀ y₀ z₀) (K₂-map (Loop2Grp-map-str (g , idp))) (loop (y₀ == y₀) (ap f x)))) ◃∙
    ap (λ q → q) (! (ap (ap (λ z → fst (K₂-rec-hom z₀ idf2G ⊙∘ K₂-map⊙ (Loop2Grp-map-str (g , idp))) z)) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x))) ◃∙
    ap (λ q → q)
      (ap (λ q → q) (∘-ap (fst (K₂-rec-hom z₀ idf2G ⊙∘ K₂-map⊙ (Loop2Grp-map-str (g , idp)))) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp)))) (loop (x₀ == x₀) x))) ◃∙
    idp ◃∙
    ap (λ q → q)
      (! (ap (λ q → q) (ap (λ q → q) (∘-ap (fst (K₂-rec-hom z₀ idf2G)) (λ z → fst (K₂-map⊙ (Loop2Grp-map-str (g , idp)) ⊙∘ K₂-map⊙ (Loop2Grp-map-str (f , idp))) z)
        (loop (x₀ == x₀) x))))) ◃∙
    idp ◃∙
    idp ◃∙
    ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (∘-ap (K₂-map (Loop2Grp-map-str (g , idp))) (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) x))) ◃∙
    ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (! (ap (ap (K₂-map (Loop2Grp-map-str (g , idp)))) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x)))) ◃∙
    ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (! (K₂-map-β-pts (Loop2Grp-map-str (g , idp)) (ap f x)))) ◃∙
    ! (ap (ap (fst (K₂-rec-hom z₀ idf2G)))
        (K₂-map-β-pts (cohmaghom (ap g) {{Loop2Grp-map-str (g , idp)}} ∘2Mσ cohmaghom (ap f) {{Loop2Grp-map-str (f , idp)}}) x)) ◃∙
    ! (ap (ap (fst (K₂-rec-hom z₀ idf2G)))
        (! (K₂-map-β-pts (cohmaghom (ap g) {{Loop2Grp-map-str (g , idp)}} ∘2Mσ cohmaghom (ap f) {{Loop2Grp-map-str (f , idp)}}) x))) ◃∙
    ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (ap (loop (z₀ == z₀)) (ap-∘ g f x))) ◃∙
    ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (K₂-map-β-pts (Loop2Grp-map-str (g ∘ f , idp)) x)) ◃∙
    ap (λ q → q) (! (ap (λ q → q) (ap-∘ (fst (K₂-rec-hom z₀ idf2G)) (λ z → fst (K₂-map⊙ (Loop2Grp-map-str (g ∘ f , idp))) z) (loop (x₀ == x₀) x)))) ◃∙
    idp ◃∙
    idp ◃∙
    idp ◃∎

  Λ₃ =
    idp ◃∙
    ! (ap (λ q → q) (! (ap-∘ (K₂-rec-y₀ x₀ z₀) (K₂-map (Loop2Grp-map-str (g ∘ f , idp))) (loop (x₀ == x₀) x)))) ◃∙
    ! (ap (λ q → q) (! (ap (ap (K₂-rec-y₀ x₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g ∘ f , idp)) x)))) ◃∙
    ! (ap (λ q → q) (! (K₂-rec-hom-β-pts z₀ (idf2G {{Loop2Grp z₀}}) (ap (g ∘ f) x)))) ◃∙
    ! (ap (λ q → q) (ap (ap (g ∘ f)) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x))) ◃∙
    ! (ap (λ q → q) (ap-∘ (g ∘ f) (K₂-rec-x₀ x₀ z₀) (loop (x₀ == x₀) x))) ◃∙
    ap (λ q → q) (ap-∘ g (λ z → f (fst (K₂-rec-hom x₀ idf2G) z)) (loop (x₀ == x₀) x)) ◃∙
    ap (ap g) (ap-∘ f (K₂-rec-x₀ x₀ y₀) (loop (x₀ == x₀) x)) ◃∙
    ap (ap g) (ap (ap f) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x)) ◃∙
    ap (ap g) (! (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f x))) ◃∙
    ap (ap g) (! (ap (ap (K₂-rec-y₀ x₀ y₀)) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x))) ◃∙
    ap (ap g) (! (ap-∘ (K₂-rec-y₀ x₀ y₀) (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) x))) ◃∙
    idp ◃∙
    ap (λ q → q) (ap (λ q → q) (∘-ap g (λ z → fst (K₂-rec-hom y₀ idf2G ⊙∘ K₂-map⊙ (Loop2Grp-map-str (f , idp))) z) (loop (x₀ == x₀) x))) ◃∙
    ap (λ q → q) (ap-∘ (fst ((g , idp) ⊙∘ K₂-rec-hom y₀ idf2G)) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp)))) (loop (x₀ == x₀) x)) ◃∙
    ap (λ q → q) (ap (ap (fst ((g , idp) ⊙∘ K₂-rec-hom y₀ idf2G))) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x)) ◃∙
    ap (λ q → q) (ap-∘ g (K₂-rec-x₀ y₀ z₀) (loop (y₀ == y₀) (ap f x))) ◃∙
    ap (λ q → q) (ap (ap g) (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f x))) ◃∙
    ap (λ q → q) (! (K₂-rec-hom-β-pts z₀ (idf2G {{Loop2Grp z₀}}) (ap g (ap f x)))) ◃∙
    ap (λ q → q) (! (ap (ap (K₂-rec-y₀ y₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g , idp)) (ap f x)))) ◃∙
    ap (λ q → q) (! (ap-∘ (K₂-rec-y₀ y₀ z₀) (K₂-map (Loop2Grp-map-str (g , idp))) (loop (y₀ == y₀) (ap f x)))) ◃∙
    ap (λ q → q) (! (ap (ap (λ z → fst (K₂-rec-hom z₀ idf2G ⊙∘ K₂-map⊙ (Loop2Grp-map-str (g , idp))) z)) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x))) ◃∙
    ap (λ q → q)
      (ap (λ q → q) (∘-ap (fst (K₂-rec-hom z₀ idf2G ⊙∘ K₂-map⊙ (Loop2Grp-map-str (g , idp)))) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp)))) (loop (x₀ == x₀) x))) ◃∙
    idp ◃∙
    ap (λ q → q)
      (! (ap (λ q → q) (ap (λ q → q) (∘-ap (fst (K₂-rec-hom z₀ idf2G)) (λ z → fst (K₂-map⊙ (Loop2Grp-map-str (g , idp)) ⊙∘ K₂-map⊙ (Loop2Grp-map-str (f , idp))) z)
        (loop (x₀ == x₀) x))))) ◃∙
    idp ◃∙
    idp ◃∙
    ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (∘-ap (K₂-map (Loop2Grp-map-str (g , idp))) (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) x))) ◃∙
    ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (! (ap (ap (K₂-map (Loop2Grp-map-str (g , idp)))) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x)))) ◃∙
    ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (! (K₂-map-β-pts (Loop2Grp-map-str (g , idp)) (ap f x)))) ◃∙
    idp ◃∙
    ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (ap (loop (z₀ == z₀)) (ap-∘ g f x))) ◃∙
    ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (K₂-map-β-pts (Loop2Grp-map-str (g ∘ f , idp)) x)) ◃∙
    ap (λ q → q) (! (ap (λ q → q) (ap-∘ (fst (K₂-rec-hom z₀ idf2G)) (λ z → fst (K₂-map⊙ (Loop2Grp-map-str (g ∘ f , idp))) z) (loop (x₀ == x₀) x)))) ◃∙
    idp ◃∙
    idp ◃∙
    idp ◃∎
