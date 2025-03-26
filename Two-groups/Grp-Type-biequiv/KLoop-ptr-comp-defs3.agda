{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import lib.PathFunctor5
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import LoopK-hom
open import KFunctor-comp
open import SqKLoop
open import apK
open import KLoop-ptr-comp-aux0

module KLoop-ptr-comp-defs3  {i j k} {X : Type i} {Y : Type j} {Z : Type k}
  {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {{ηZ : has-level 2 Z}}
  (f : X → Y) (g : Y → Z) (x₀ : X) (x : x₀ == x₀) where

  open import KLoop-ptr-comp-defs f g x₀ x

  open KLPC-aux0 f g x₀ x

  ρ₁ = 
    hnat-∙'-!ap-!ap∙-=ₛ g (fst (K₂-rec-hom z₀ idf2G)) (loop (x₀ == x₀) x)
      {H₁ = fst (sq-KΩ x₀ z₀ (g ∘ f , idp))}
      {H₂ = fst (sq-KΩ x₀ y₀ (f , idp))}
      (λ u → fst (sq-KΩ y₀ z₀ (g , idp)) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp))) u))
      {H₄ = fst (apK₂ (Loop2Grp-map-∘ (g , idp) (f , idp)))}
      {H₅ = fst (K₂-map-∘ (Loop2Grp-map-str (f , idp)) (Loop2Grp-map-str (g , idp)))}
      σ₁ σ₂ σ₄ σ₅
      K₂-β-1 K₂-β-2 K₂-β-4 K₂-β-5

  ρ₂ = hnat-∙'-pre (fst (sq-KΩ y₀ z₀ (g , idp))) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp)))) (loop (x₀ == x₀) x)
