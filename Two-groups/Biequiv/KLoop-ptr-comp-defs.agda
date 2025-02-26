{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import LoopK
open import SqKLoop
open import K-hom-ind

module KLoop-ptr-comp-defs  {i j k} {X : Type i} {Y : Type j} {Z : Type k}
  {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {{ηZ : has-level 2 Z}}
  (f : X → Y) (g : Y → Z) (x₀ : X) (x : x₀ == x₀) where

  y₀ = f x₀
  z₀ = g (f x₀)
    
  σ₁ = 
    ap-∘ (g ∘ f) (K₂-rec-x₀ x₀ z₀) (loop (x₀ == x₀) x) ◃∙
    ap (ap (g ∘ f)) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x) ◃∙
    ! (K₂-rec-hom-β-pts z₀ (idf2G {{Loop2Grp z₀}}) (ap (g ∘ f) x)) ◃∙
    ! (ap (ap (K₂-rec-y₀ x₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g ∘ f , idp)) x)) ◃∙
    ! (ap-∘ (K₂-rec-y₀ x₀ z₀) (K₂-map (Loop2Grp-map-str (g ∘ f , idp))) (loop (x₀ == x₀) x)) ◃∎
    
  σ₂ =
    ap-∘ f (K₂-rec-x₀ x₀ y₀) (loop (x₀ == x₀) x) ◃∙
    ap (ap f) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x) ◃∙
    ! (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f x)) ◃∙
    ! (ap (ap (K₂-rec-y₀ x₀ y₀)) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x)) ◃∙
    ! (ap-∘ (K₂-rec-y₀ x₀ y₀) (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) x)) ◃∎

  σ₃ =
    ap-∘ g (K₂-rec-x₀ y₀ z₀) (loop (y₀ == y₀) (ap f x)) ◃∙
    ap (ap g) (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f x)) ◃∙
    ! (K₂-rec-hom-β-pts z₀ (idf2G {{Loop2Grp z₀}}) (ap g (ap f x))) ◃∙
    ! (ap (ap (K₂-rec-y₀ y₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g , idp)) (ap f x))) ◃∙
    ! (ap-∘ (K₂-rec-y₀ y₀ z₀) (K₂-map (Loop2Grp-map-str (g , idp))) (loop (y₀ == y₀) (ap f x))) ◃∎

  σ₄ =
    K₂-map-β-pts (Loop2Grp-map-str (g ∘ f , idp)) x ◃∙
    ap (loop (z₀ == z₀)) (ap-∘ g f x) ◃∙
    ! (K₂-map-β-pts (cohmaghom (ap g) {{Loop2Grp-map-str (g , idp)}} ∘2Mσ cohmaghom (ap f) {{Loop2Grp-map-str (f , idp)}}) x) ◃∎

  σ₅ =
    K₂-map-β-pts (cohgrphom (ap g) {{Loop2Grp-map-str (g , idp)}} ∘2Gσ cohgrphom (ap f) {{Loop2Grp-map-str (f , idp)}}) x ◃∙
    ! (K₂-map-β-pts (Loop2Grp-map-str (g , idp)) (ap f x)) ◃∙
    ! (ap (ap (K₂-map (Loop2Grp-map-str (g , idp)))) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x)) ◃∙
    ∘-ap (K₂-map (Loop2Grp-map-str (g , idp))) (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) x) ◃∎

  ν₁ =
    (λ v →
      ap-∘ (g ∘ f) (K₂-rec-x₀ x₀ z₀) (loop (x₀ == x₀) v) ∙
      ap (ap (g ∘ f)) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) v) ∙
      ! (K₂-rec-hom-β-pts z₀ (idf2G {{Loop2Grp z₀}}) (ap (g ∘ f) v)) ∙
      ! (ap (ap (K₂-rec-y₀ x₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g ∘ f , idp)) v)) ∙
      ! (ap-∘ (K₂-rec-y₀ x₀ z₀) (K₂-map (Loop2Grp-map-str (g ∘ f , idp))) (loop (x₀ == x₀) v)))

  ν₂ =
    (λ v →
      ap-∘ f (K₂-rec-x₀ x₀ y₀) (loop (x₀ == x₀) v) ∙
      ap (ap f) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) v) ∙
      ! (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f v)) ∙
      ! (ap (ap (K₂-rec-y₀ x₀ y₀)) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) v)) ∙
      ! (ap-∘ (K₂-rec-y₀ x₀ y₀) (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) v)))

  ν₄ = 
    (λ v →
      K₂-map-β-pts (Loop2Grp-map-str (g ∘ f , idp)) v ∙
      ap (loop (z₀ == z₀)) (ap-∘ g f v) ∙
      ! (K₂-map-β-pts (cohmaghom (ap g) {{Loop2Grp-map-str (g , idp)}} ∘2Mσ cohmaghom (ap f) {{Loop2Grp-map-str (f , idp)}}) v))

  ν₅ = 
    (λ v →
      K₂-map-β-pts (cohgrphom (ap g) {{Loop2Grp-map-str (g , idp)}} ∘2Gσ cohgrphom (ap f) {{Loop2Grp-map-str (f , idp)}}) v ∙
      ! (K₂-map-β-pts (Loop2Grp-map-str (g , idp)) (ap f v)) ∙
      ! (ap (ap (K₂-map (Loop2Grp-map-str (g , idp)))) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) v)) ∙
      ∘-ap (K₂-map (Loop2Grp-map-str (g , idp))) (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) v))
