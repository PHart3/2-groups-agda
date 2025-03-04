{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import SqKLoop
open import LoopK

module KLoop-ptr-comp-aux6 where

module KLPC-aux6 {i j k} {X : Type i} {Y : Type j} {Z : Type k}
  {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {{ηZ : has-level 2 Z}}
  (f : X → Y) (g : Y → Z) (x₀ : X) (x : x₀ == x₀) where

  open import KLoop-ptr-comp-defs f g x₀ x

  abstract
    β-pts-red2 :
      ap (ap g) (! (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f x))) ◃∙
      ∘-ap g (K₂-rec-y₀ x₀ y₀) (loop (y₀ == y₀) (ap f x)) ◃∙
      ap (λ q → q) (ap-∘ g (K₂-rec-x₀ y₀ z₀) (loop (y₀ == y₀) (ap f x))) ◃∙
      ap (λ q → q) (ap (ap g) (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f x))) ◃∎
        =ₛ
      idp ◃∎
    β-pts-red2 =
      ap (ap g) (! (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f x))) ◃∙
      ∘-ap g (K₂-rec-y₀ x₀ y₀) (loop (y₀ == y₀) (ap f x)) ◃∙
      ap (λ q → q) (ap-∘ g (K₂-rec-x₀ y₀ z₀) (loop (y₀ == y₀) (ap f x))) ◃∙
      ap (λ q → q) (ap (ap g) (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f x))) ◃∎
        =ₛ⟨ 2 & 2 & =ₛ-in (ap2 _∙_ (ap-idf (ap-∘ g (K₂-rec-x₀ y₀ z₀) (loop (y₀ == y₀) (ap f x)))) (ap-idf (ap (ap g) (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f x)))))  ⟩
      ap (ap g) (! (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f x))) ◃∙
      ∘-ap g (K₂-rec-y₀ x₀ y₀) (loop (y₀ == y₀) (ap f x)) ◃∙
      ap-∘ g (K₂-rec-x₀ y₀ z₀) (loop (y₀ == y₀) (ap f x)) ◃∙
      ap (ap g) (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f x)) ◃∎
        =ₛ₁⟨ 1 & 2 & ∘-ap-ap-∘-inv g (K₂-rec-y₀ x₀ y₀) (loop (y₀ == y₀) (ap f x)) ⟩
      ap (ap g) (! (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f x))) ◃∙
      idp ◃∙
      ap (ap g) (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f x)) ◃∎
        =ₛ₁⟨ ap-!-inv-l (ap g) (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f x)) ⟩
      idp ◃∎ ∎ₛ
