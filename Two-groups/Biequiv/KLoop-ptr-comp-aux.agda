{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=2 --lossy-unification #-}

open import lib.Basics
open import lib.PathFunctor5
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import K-hom-ind
open import LoopK
open import KFunctor-comp
open import SqKLoop
open import apK

module KLoop-ptr-comp-aux where

  module _ {i j k} {X : Type i} {Y : Type j} {Z : Type k}
    {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {{ηZ : has-level 2 Z}}
    (f : X → Y) (g : Y → Z) (x₀ : X) (x : x₀ == x₀) where
    
    open import KLoop-ptr-comp-defs f g x₀ x

    test =
      hmtpy-nat-∙'
        (λ u →
          ! (fst (sq-KΩ x₀ z₀ (g ∘ f , idp)) u) ∙
          ap g (fst (sq-KΩ x₀ y₀ (f , idp)) u) ∙
          fst (sq-KΩ y₀ z₀ (g , idp)) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp))) u) ∙
          ! (ap (fst (K₂-rec-hom z₀ idf2G)) (fst (apK₂ (Loop2Grp-map-∘ (g , idp) (f , idp))) u ∙
            fst (K₂-map-∘ (Loop2Grp-map-str (f , idp)) (Loop2Grp-map-str (g , idp))) u)))
        (loop (x₀ == x₀) x) ◃∎
        =ₛ⟨
          hnat-∙'-!ap-!ap∙-=ₛ g (fst (K₂-rec-hom z₀ idf2G)) (loop (x₀ == x₀) x)
            {H₁ = fst (sq-KΩ x₀ z₀ (g ∘ f , idp))}
            {H₂ = fst (sq-KΩ x₀ y₀ (f , idp))}
            (λ u → fst (sq-KΩ y₀ z₀ (g , idp)) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp))) u))
            {H₄ = fst (apK₂ (Loop2Grp-map-∘ (g , idp) (f , idp)))}
            {H₅ = fst (K₂-map-∘ (Loop2Grp-map-str (f , idp)) (Loop2Grp-map-str (g , idp)))}
            σ₁
            σ₂
            σ₄
            σ₅
            (K₂-∼-ind-β
              (g ∘ f ∘ K₂-rec-x₀ x₀ z₀)
              (K₂-rec-y₀ x₀ z₀ ∘ K₂-map (Loop2Grp-map-str (g ∘ f , idp)))
              idp
              (λ v →
                ap-∘ (g ∘ f) (K₂-rec-x₀ x₀ z₀) (loop (x₀ == x₀) v) ∙
                ap (ap (g ∘ f)) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) v) ∙
                ! (K₂-rec-hom-β-pts z₀ (idf2G {{Loop2Grp z₀}}) (ap (g ∘ f) v)) ∙
                ! (ap (ap (K₂-rec-y₀ x₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g ∘ f , idp)) v)) ∙
                ! (ap-∘ (K₂-rec-y₀ x₀ z₀) (K₂-map (Loop2Grp-map-str (g ∘ f , idp))) (loop (x₀ == x₀) v)))
              _ x)
            (K₂-∼-ind-β
              (f ∘ K₂-rec-x₀ x₀ y₀)
              (K₂-rec-y₀ x₀ y₀ ∘ K₂-map (Loop2Grp-map-str (f , idp)))
              idp
              (λ v →
                ap-∘ f (K₂-rec-x₀ x₀ y₀) (loop (x₀ == x₀) v) ∙
                ap (ap f) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) v) ∙
                ! (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f v)) ∙
                ! (ap (ap (K₂-rec-y₀ x₀ y₀)) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) v)) ∙
                ! (ap-∘ (K₂-rec-y₀ x₀ y₀) (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) v)))
              _ x)
            ρ₁
            (K₂-∼-ind-β
              (map₁-∘ (Loop2Grp-map-str (f , idp)) (Loop2Grp-map-str (g , idp)))
              (map₂-∘ (Loop2Grp-map-str (f , idp)) (Loop2Grp-map-str (g , idp)))
              idp
              (λ v →
                K₂-map-β-pts (cohgrphom (ap g) {{Loop2Grp-map-str (g , idp)}} ∘2Gσ cohgrphom (ap f) {{Loop2Grp-map-str (f , idp)}}) v ∙
                ! (K₂-map-β-pts (Loop2Grp-map-str (g , idp)) (ap f v)) ∙
                ! (ap (ap (K₂-map (Loop2Grp-map-str (g , idp)))) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) v)) ∙
                ∘-ap (K₂-map (Loop2Grp-map-str (g , idp))) (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) v))
              _ x) ⟩
      ?
{-
    abstract
      KLoop-∘-coher :
        hmtpy-nat-∙'
          (λ u →
            ! (fst (sq-KΩ x₀ z₀ (g ∘ f , idp)) u) ∙
            ap g (fst (sq-KΩ x₀ y₀ (f , idp)) u) ∙
            fst (sq-KΩ y₀ z₀ (g , idp)) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp))) u) ∙
            ! (ap (fst (K₂-rec-hom z₀ idf2G)) (fst (apK₂ (Loop2Grp-map-∘ (g , idp) (f , idp))) u ∙
              fst (K₂-map-∘ (Loop2Grp-map-str (f , idp)) (Loop2Grp-map-str (g , idp))) u)))
          (loop (x₀ == x₀) x) ◃∎
          =ₛ
        hmtpy-nat-∙' (λ u → idp) (loop (x₀ == x₀) x) ◃∎ 
      KLoop-∘-coher =
        hnat-∙'-!ap-!ap∙-=ₛ g (fst (K₂-rec-hom z₀ idf2G)) (loop (x₀ == x₀) x)
        {H₁ = fst (sq-KΩ x₀ z₀ (g ∘ f , idp))}
        {H₂ = fst (sq-KΩ x₀ y₀ (f , idp))}
        (λ u → fst (sq-KΩ y₀ z₀ (g , idp)) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp))) u))
        {H₄ = fst (apK₂ (Loop2Grp-map-∘ (g , idp) (f , idp)))}
        {H₅ = fst (K₂-map-∘ (Loop2Grp-map-str (f , idp)) (Loop2Grp-map-str (g , idp)))}
        σ₁
        σ₂
        σ₄
        σ₅
        (K₂-∼-ind-β
          (g ∘ f ∘ K₂-rec-x₀ x₀ z₀)
          (K₂-rec-y₀ x₀ z₀ ∘ K₂-map (Loop2Grp-map-str (g ∘ f , idp)))
          idp
          (λ v →
            ap-∘ (g ∘ f) (K₂-rec-x₀ x₀ z₀) (loop (x₀ == x₀) v) ∙
            ap (ap (g ∘ f)) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) v) ∙
            ! (K₂-rec-hom-β-pts z₀ (idf2G {{Loop2Grp z₀}}) (ap (g ∘ f) v)) ∙
            ! (ap (ap (K₂-rec-y₀ x₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g ∘ f , idp)) v)) ∙
            ! (ap-∘ (K₂-rec-y₀ x₀ z₀) (K₂-map (Loop2Grp-map-str (g ∘ f , idp))) (loop (x₀ == x₀) v)))
          _ x)
        (K₂-∼-ind-β
          (f ∘ K₂-rec-x₀ x₀ y₀)
          (K₂-rec-y₀ x₀ y₀ ∘ K₂-map (Loop2Grp-map-str (f , idp)))
          idp
          (λ v →
            ap-∘ f (K₂-rec-x₀ x₀ y₀) (loop (x₀ == x₀) v) ∙
            ap (ap f) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) v) ∙
            ! (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f v)) ∙
            ! (ap (ap (K₂-rec-y₀ x₀ y₀)) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) v)) ∙
            ! (ap-∘ (K₂-rec-y₀ x₀ y₀) (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) v)))
          _ x)
        ρ₁
        (K₂-∼-ind-β
          (map₁-∘ (Loop2Grp-map-str (f , idp)) (Loop2Grp-map-str (g , idp)))
          (map₂-∘ (Loop2Grp-map-str (f , idp)) (Loop2Grp-map-str (g , idp)))
          idp
          (λ v →
            K₂-map-β-pts (cohgrphom (ap g) {{Loop2Grp-map-str (g , idp)}} ∘2Gσ cohgrphom (ap f) {{Loop2Grp-map-str (f , idp)}}) v ∙
            ! (K₂-map-β-pts (Loop2Grp-map-str (g , idp)) (ap f v)) ∙
            ! (ap (ap (K₂-map (Loop2Grp-map-str (g , idp)))) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) v)) ∙
            ∘-ap (K₂-map (Loop2Grp-map-str (g , idp))) (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) v))
          _ x) -}
