{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import K-hom-ind
open import KFunctor-comp
open import SqKLoop
open import apK

module KLoop-ptr-comp-aux0 where

  module KLPC-aux0 {i j k} {X : Type i} {Y : Type j} {Z : Type k}
    {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {{ηZ : has-level 2 Z}}
    (f : X → Y) (g : Y → Z) (x₀ : X) (x : x₀ == x₀) where
    
    open import KLoop-ptr-comp-defs f g x₀ x

    abstract

      K₂-β-1 : hmpty-nat-∙' (fst (sq-KΩ x₀ z₀ (g ∘ f , idp))) (loop (x₀ == x₀) x) == ↯ σ₁
      K₂-β-1 =
        K₂-∼-ind-β
          (g ∘ f ∘ K₂-rec-x₀ x₀ z₀)
          (K₂-rec-y₀ x₀ z₀ ∘ K₂-map (Loop2Grp-map-str (g ∘ f , idp)))
          idp
          ν₁
          _ x

      K₂-β-2 : hmpty-nat-∙' (fst (sq-KΩ x₀ y₀ (f , idp))) (loop (x₀ == x₀) x) == ↯ σ₂
      K₂-β-2 =
        K₂-∼-ind-β
          (f ∘ K₂-rec-x₀ x₀ y₀)
          (K₂-rec-y₀ x₀ y₀ ∘ K₂-map (Loop2Grp-map-str (f , idp)))
          idp
          ν₂
          _ x

      K₂-β-4 : hmpty-nat-∙' (fst (apK₂ (Loop2Grp-map-∘ (g , idp) (f , idp)))) (loop (x₀ == x₀) x) == ↯ σ₄
      K₂-β-4 =
        K₂-∼-ind-β
          (fst (K₂-map⊙ (Loop2Grp-map-str (g ∘ f , idp))))
          (fst (K₂-map⊙ (cohmaghom (ap g) {{Loop2Grp-map-str (g , idp)}} ∘2Mσ cohmaghom (ap f) {{Loop2Grp-map-str (f , idp)}})))
          idp
          ν₄
          _ x

      K₂-β-5 : hmpty-nat-∙' (fst (K₂-map-∘ (Loop2Grp-map-str (f , idp)) (Loop2Grp-map-str (g , idp)))) (loop (x₀ == x₀) x) == ↯ σ₅
      K₂-β-5 =
        K₂-∼-ind-β
          (map₁-∘ (Loop2Grp-map-str (f , idp)) (Loop2Grp-map-str (g , idp)))
          (map₂-∘ (Loop2Grp-map-str (f , idp)) (Loop2Grp-map-str (g , idp)))
          idp
          ν₅
          _ x
