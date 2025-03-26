{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import SqKLoop
open import LoopK-hom

module KLoop-ptr-comp-aux7 where

module KLPC-aux7 {i j k} {X : Type i} {Y : Type j} {Z : Type k}
  {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {{ηZ : has-level 2 Z}}
  (f : X → Y) (g : Y → Z) (x₀ : X) (x : x₀ == x₀) where

  open import KLoop-ptr-comp-defs f g x₀ x

  abstract
    β-pts-red4 :
      ap (λ q → q) (! (ap (ap (K₂-rec-y₀ y₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g , idp)) (ap f x)))) ◃∙
      ap (λ q → q) (! (ap-∘ (K₂-rec-y₀ y₀ z₀) (K₂-map (Loop2Grp-map-str (g , idp))) (loop (y₀ == y₀) (ap f x)))) ◃∙
      ap-∘ (fst (K₂-rec-hom z₀ idf2G)) (K₂-map (Loop2Grp-map-str (g , idp))) (loop (y₀ == y₀) (ap f x)) ◃∙
      ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (! (K₂-map-β-pts (Loop2Grp-map-str (g , idp)) (ap f x)))) ◃∎
        =ₛ
      idp ◃∎
    β-pts-red4 =
      ap (λ q → q) (! (ap (ap (K₂-rec-y₀ y₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g , idp)) (ap f x)))) ◃∙
      ap (λ q → q) (! (ap-∘ (K₂-rec-y₀ y₀ z₀) (K₂-map (Loop2Grp-map-str (g , idp))) (loop (y₀ == y₀) (ap f x)))) ◃∙
      ap-∘ (fst (K₂-rec-hom z₀ idf2G)) (K₂-map (Loop2Grp-map-str (g , idp))) (loop (y₀ == y₀) (ap f x)) ◃∙
      ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (! (K₂-map-β-pts (Loop2Grp-map-str (g , idp)) (ap f x)))) ◃∎
        =ₑ⟨ 0 & 2 &
          (! (ap (ap (K₂-rec-y₀ y₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g , idp)) (ap f x))) ◃∙
          ! (ap-∘ (K₂-rec-y₀ y₀ z₀) (K₂-map (Loop2Grp-map-str (g , idp))) (loop (y₀ == y₀) (ap f x))) ◃∎)
          % =ₛ-in $
            ap2 _∙_
              (ap-idf (! (ap (ap (K₂-rec-y₀ y₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g , idp)) (ap f x)))))
              (ap-idf (! (ap-∘ (K₂-rec-y₀ y₀ z₀) (K₂-map (Loop2Grp-map-str (g , idp))) (loop (y₀ == y₀) (ap f x))))) ⟩
      ! (ap (ap (K₂-rec-y₀ y₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g , idp)) (ap f x))) ◃∙
      ! (ap-∘ (K₂-rec-y₀ y₀ z₀) (K₂-map (Loop2Grp-map-str (g , idp))) (loop (y₀ == y₀) (ap f x))) ◃∙
      ap-∘ (fst (K₂-rec-hom z₀ idf2G)) (K₂-map (Loop2Grp-map-str (g , idp))) (loop (y₀ == y₀) (ap f x)) ◃∙
      ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (! (K₂-map-β-pts (Loop2Grp-map-str (g , idp)) (ap f x)))) ◃∎
        =ₛ₁⟨ 1 & 2 & !-inv-l (ap-∘ (K₂-rec-y₀ y₀ z₀) (K₂-map (Loop2Grp-map-str (g , idp))) (loop (y₀ == y₀) (ap f x))) ⟩
      ! (ap (ap (K₂-rec-y₀ y₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g , idp)) (ap f x))) ◃∙
      idp ◃∙
      ! (ap (ap (fst (K₂-rec-hom z₀ idf2G))) (! (K₂-map-β-pts (Loop2Grp-map-str (g , idp)) (ap f x)))) ◃∎
        =ₛ₁⟨ ap-!-!-inv (ap (K₂-rec-y₀ y₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g , idp)) (ap f x)) ⟩
      idp ◃∎ ∎ₛ
