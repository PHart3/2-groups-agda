{-# OPTIONS --without-K --rewriting --lossy-unification --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import LoopK-hom
open import SqKLoop-aux-defs2

module SqKLoop-aux6 where

module Sq-aux6 {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} (x₀ : X) (f : X → Y) where

  y₀ = f x₀
  Λx₀ = wkmag-to-loop x₀ (cohmaghom (idf (x₀ == x₀)) {{idf2G}})
  Λy₀ = wkmag-to-loop y₀ (cohmaghom (idf (y₀ == y₀)) {{idf2G}})
  K₂-rec-x₀ = K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)
  K₂-rec-y₀ = K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)
  K₂-rec-y₀-∘ = K₂-rec-y₀ ∘ K₂-map (Loop2Grp-map-str (f , idp))

  ζ₃-free : {b : _} (c : base (x₀ == x₀) == b)
    →
    ap (f ∘ K₂-rec-x₀) c
      ==
    ap f (ap (fst (K₂-rec-hom x₀ idf2G)) c)
  ζ₃-free idp = idp

  ζ₄-free : {b : _} (c : b == base (x₀ == x₀))
    →
    ap (K₂-rec-y₀ ∘ K₂-map (Loop2Grp-map-str (f , idp))) c
      ==
    ap (fst (K₂-rec-hom y₀ idf2G)) (ap (K₂-map (Loop2Grp-map-str (f , idp))) c)
  ζ₄-free idp = idp

  abstract

    ζ₃-red-aux : {b : _} (c₁ : b == base (x₀ == x₀)) (c₂ : base (x₀ == x₀) == b)
      →
      ! (ap (λ u → u ∙ ap (f ∘ K₂-rec-x₀) c₂)
          (ap-∘ f K₂-rec-x₀ c₁)) ∙
      ∙-ap (f ∘ K₂-rec-x₀) c₁ c₂ ∙
      ap-∘ f K₂-rec-x₀ (c₁ ∙ c₂) ∙
      ap (ap f) (! (∙-ap (fst (K₂-rec-hom x₀ idf2G)) c₁ c₂ ∙ idp)) ∙
      ! (! (ap (λ z → z)
          (ap-∙ f (ap K₂-rec-x₀ c₁)
            (ap (fst (K₂-rec-hom x₀ idf2G)) c₂)))) ∙ idp
        ==
      ap (_∙_ (ap f (ap K₂-rec-x₀ c₁)))
        (ζ₃-free c₂)
    ζ₃-red-aux idp c₂ = lemma c₂
      where
        lemma : {b : _} (c : base (x₀ == x₀) == b) →
          ap-∘ f K₂-rec-x₀ c ∙ idp
            ==
          ap (λ q → q) (ζ₃-free c)
        lemma idp = idp

    ζ₄-red-aux : {b : _} (c₁ : b == base (x₀ == x₀)) (c₂ : base (x₀ == x₀) == b)
      →
      ! (ap (_∙_
          (ap K₂-rec-y₀-∘  c₁))
        (ap-∘ f K₂-rec-x₀ c₂)) ∙
      ! (ap (λ u → u ∙ ap (f ∘  K₂-rec-x₀) c₂)
          (! (ap-∘ K₂-rec-y₀ (K₂-map (Loop2Grp-map-str (f , idp))) c₁))) ∙
      ap (_∙_ (ap (fst (K₂-rec-hom y₀ idf2G)) (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁))) (ζ₃-free c₂) ∙ idp
        ==
      ap (λ q → q ∙ ap f (ap (fst (K₂-rec-hom x₀ idf2G)) c₂)) (ζ₄-free c₁)
    ζ₄-red-aux idp c₂ = lemma c₂
      where
        lemma : {b : _} (c : base (x₀ == x₀) == b) →
          ! (ap (λ q → q) (ap-∘ f K₂-rec-x₀ c)) ∙
          ap (λ q → q) (ζ₃-free c) ∙ idp
            ==
          idp
        lemma idp = idp

  module Sq-aux6-red (c₁ c₂ : base (x₀ == x₀) == base (x₀ == x₀)) where

    abstract

      ζ₃-red : {p : y₀ == y₀} 
        (ζ :
          p
            ==
          ap f (ap K₂-rec-x₀ c₁)) → 
        ! (ap (λ u → u ∙ ap (f ∘  K₂-rec-x₀) c₂) (! ζ)) ◃∙
        ! (ap (λ u → u ∙ ap (f ∘  K₂-rec-x₀) c₂)
            (ap-∘ f K₂-rec-x₀ c₁)) ◃∙
        ∙-ap (f ∘  K₂-rec-x₀) c₁ c₂ ◃∙
        ap-∘ f K₂-rec-x₀ (c₁ ∙ c₂) ◃∙
        ap (ap f) (! (∙-ap (fst (K₂-rec-hom x₀ idf2G)) c₁ c₂ ∙ idp)) ◃∙
        ! (! (ap (λ z → z)
          (ap-∙ f (ap K₂-rec-x₀ c₁) (ap (fst (K₂-rec-hom x₀ idf2G)) c₂)))) ◃∙
        ! (ap (λ u → u ∙ ap f (ap (fst (K₂-rec-hom x₀ idf2G)) c₂)) ζ) ◃∎
          =ₛ
        ap (λ q → p ∙ q) (ζ₃-free c₂) ◃∎
      ζ₃-red idp = =ₛ-in (ζ₃-red-aux c₁ c₂)

      ζ₄-red : {p : y₀ == y₀} 
        (ζ :
          p
            ==
          ap f (ap (fst (K₂-rec-hom x₀ idf2G)) c₂)) → 
        ! (ap (_∙_
            (ap K₂-rec-y₀-∘ c₁)) (! ζ)) ◃∙
        ! (ap (_∙_ (ap K₂-rec-y₀-∘ c₁))
            (ap-∘ f K₂-rec-x₀ c₂)) ◃∙
        ! (ap (λ u → u ∙ ap (f ∘ K₂-rec-x₀) c₂)
             (! (ap-∘ K₂-rec-y₀ (K₂-map (Loop2Grp-map-str (f , idp))) c₁))) ◃∙
        ap (λ q → ap (fst (K₂-rec-hom y₀ idf2G)) (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁) ∙ q) (ζ₃-free c₂) ◃∙
        ! (ap (_∙_ (ap (fst (K₂-rec-hom y₀ idf2G)) (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁))) ζ) ◃∎
          =ₛ
        ap (λ q → q ∙ p) (ζ₄-free c₁) ◃∎
      ζ₄-red idp = =ₛ-in (ζ₄-red-aux c₁ c₂)
