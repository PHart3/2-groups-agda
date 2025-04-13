{-# OPTIONS --without-K --rewriting --lossy-unification --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import 2Semigroup
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import LoopK-hom

module SqKLoop-aux-defs1 where

module _ {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} (x₀ : X)
  (f : X → Y) (x y : x₀ == x₀) where

  private
    y₀ = f x₀
    Λx₀ = wksgrp-to-loop x₀ (cohsgrphom (idf (x₀ == x₀)) {{idf2G}})
    Λy₀ = wksgrp-to-loop y₀ (cohsgrphom (idf (y₀ == y₀)) {{idf2G}})
    
  module SqKLoop-abb1 where

    δ₁ =
      ∙-ap (f ∘ K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀))
        (loop (x₀ == x₀) x) (loop (x₀ == x₀) y) ◃∙
      ap (ap (f ∘ K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)))
        (loop-comp (x₀ == x₀) x y) ◃∙
      ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀))
        (loop (x₀ == x₀) (x ∙ y)) ◃∙
      ap (ap f)
        (! (∙-ap (fst (K₂-rec-hom x₀ idf2G)) (loop (x₀ == x₀) x) (loop (x₀ == x₀) y) ∙
           ap (ap (fst (K₂-rec-hom x₀ idf2G))) (loop-comp (x₀ == x₀) x y))) ◃∙
      ap (ap f)
        (ap2 _∙_
          (K₂-rec-hom-β-pts x₀ idf2G x)
          (K₂-rec-hom-β-pts x₀ idf2G y)) ◃∙
      idp ◃∙
      ! (! (ap (λ z → z) (ap-∙ f x y))) ◃∙
      ! (K₂-rec-hom-β-pts y₀ idf2G (ap f x ∙ ap f y)) ◃∙
      ! (ap (λ z → ap (fst (K₂-rec-hom y₀ idf2G)) (loop (y₀ == y₀) z)) (ap-∙ f x y)) ◃∙
      ! (ap
          (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
          (ap (loop (y₀ == y₀)) (∙-ap f x y))) ◃∙
      ! (ap
          (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
          (loop-comp (y₀ == y₀) (ap f x) (ap f y))) ◃∙
      ! (ap
          (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
          (ap2 _∙_ (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) y))) ◃∙
      ! (ap
          (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
          (! (∙-ap (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) x) (loop (x₀ == x₀) y)))) ◃∙
      ! (ap
          (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
          (! (ap (ap (K₂-map (Loop2Grp-map-str (f , idp)))) (loop-comp (x₀ == x₀) x y)))) ◃∙
      ! (ap-∘ (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)) (K₂-map (Loop2Grp-map-str (f , idp)))
          (loop (x₀ == x₀) (x ∙ y))) ◃∎

    δ₂ =
      ∙-ap (f ∘ K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀))
        (loop (x₀ == x₀) x) (loop (x₀ == x₀) y) ◃∙
      ap (ap (f ∘ K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)))
        (loop-comp (x₀ == x₀) x y) ◃∙
      ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀))
        (loop (x₀ == x₀) (x ∙ y)) ◃∙
      ap (ap f)
        (! (∙-ap (fst (K₂-rec-hom x₀ idf2G)) (loop (x₀ == x₀) x) (loop (x₀ == x₀) y) ∙
           ap (ap (fst (K₂-rec-hom x₀ idf2G))) (loop-comp (x₀ == x₀) x y))) ◃∙
      ap (ap f)
        (ap2 _∙_
          (K₂-rec-hom-β-pts x₀ idf2G x)
          (K₂-rec-hom-β-pts x₀ idf2G y)) ◃∙
      idp ◃∙
      ! (! (ap (λ z → z) (ap-∙ f x y))) ◃∙
      idp ◃∙
      ! (ap2 _∙_ (K₂-rec-hom-β-pts y₀ idf2G (ap f x)) (K₂-rec-hom-β-pts y₀ idf2G (ap f y))) ◃∙
      ! (!
          (∙-ap (fst (K₂-rec-hom y₀ idf2G)) (loop (y₀ == y₀) (ap f x)) (loop (y₀ == y₀) (ap f y)) ∙
          ap (ap (fst (K₂-rec-hom y₀ idf2G))) (loop-comp (y₀ == y₀) (ap f x) (ap f y)))) ◃∙
      ! (ap (λ z → ap (fst (K₂-rec-hom y₀ idf2G)) (loop (y₀ == y₀) z)) (ap-∙ f x y)) ◃∙
      ! (ap
          (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
          (ap (loop (y₀ == y₀)) (∙-ap f x y))) ◃∙
      ! (ap
          (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
          (loop-comp (y₀ == y₀) (ap f x) (ap f y))) ◃∙
      ! (ap
          (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
          (ap2 _∙_ (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) y))) ◃∙
      ! (ap
          (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
          (! (∙-ap (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) x) (loop (x₀ == x₀) y)))) ◃∙
      ! (ap
          (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
          (! (ap (ap (K₂-map (Loop2Grp-map-str (f , idp)))) (loop-comp (x₀ == x₀) x y)))) ◃∙
      ! (ap-∘ (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)) (K₂-map (Loop2Grp-map-str (f , idp)))
          (loop (x₀ == x₀) (x ∙ y))) ◃∎

    ϕ₁ =
      ! (ap (λ z → ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)) (ap (K₂-map (Loop2Grp-map-str (f , idp))) z))
          (loop-comp (x₀ == x₀) x y))
    ϕ₂ =
      ap (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀) ∘ K₂-map (Loop2Grp-map-str (f , idp))))
        (loop-comp (x₀ == x₀) x y)

    δ₃ =
      ∙-ap (f ∘ K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀))
        (loop (x₀ == x₀) x) (loop (x₀ == x₀) y) ◃∙
      ap (ap (f ∘ K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)))
        (loop-comp (x₀ == x₀) x y) ◃∙
      ! (ap (ap (f ∘ K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀))) (loop-comp (x₀ == x₀) x y)) ◃∙
      ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) (loop (x₀ == x₀) x ∙ loop (x₀ == x₀) y) ◃∙
      ap (λ z → ap f (ap (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀ ) (loop-assoc' Λx₀)) z)) (loop-comp (x₀ == x₀) x y) ◃∙
      ap (ap f)
        (! (∙-ap (fst (K₂-rec-hom x₀ idf2G)) (loop (x₀ == x₀) x) (loop (x₀ == x₀) y) ∙
           ap (ap (fst (K₂-rec-hom x₀ idf2G))) (loop-comp (x₀ == x₀) x y))) ◃∙
      ap (ap f)
        (ap2 _∙_
          (K₂-rec-hom-β-pts x₀ idf2G x)
          (K₂-rec-hom-β-pts x₀ idf2G y)) ◃∙
      idp ◃∙
      ! (! (ap (λ z → z) (ap-∙ f x y))) ◃∙
      idp ◃∙
      ! (ap2 _∙_ (K₂-rec-hom-β-pts y₀ idf2G (ap f x)) (K₂-rec-hom-β-pts y₀ idf2G (ap f y))) ◃∙
      ! (!
          (∙-ap (fst (K₂-rec-hom y₀ idf2G)) (loop (y₀ == y₀) (ap f x)) (loop (y₀ == y₀) (ap f y)) ∙
          ap (ap (fst (K₂-rec-hom y₀ idf2G))) (loop-comp (y₀ == y₀) (ap f x) (ap f y)))) ◃∙
      idp ◃∙
      ! (ap
          (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
          (loop-comp (y₀ == y₀) (ap f x) (ap f y))) ◃∙
      ! (ap
          (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
          (ap2 _∙_ (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) y))) ◃∙
      ! (ap
          (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
          (! (∙-ap (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) x) (loop (x₀ == x₀) y)))) ◃∙
      ! (ap
          (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
          (! (ap (ap (K₂-map (Loop2Grp-map-str (f , idp)))) (loop-comp (x₀ == x₀) x y)))) ◃∙
      ϕ₁ ◃∙
      ! (ap-∘ (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)) (K₂-map (Loop2Grp-map-str (f , idp)))
          (loop (x₀ == x₀) x ∙ loop (x₀ == x₀) y)) ◃∙
      ϕ₂ ◃∎

    δ₄ = 
      ap2 _∙_
        (ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀))
          (loop (x₀ == x₀) x) ∙
        ap (ap f) (K₂-rec-hom-β-pts x₀ idf2G x) ∙
        ! (K₂-rec-hom-β-pts y₀ idf2G (ap f x)) ∙
        ! (ap (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
             (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x)) ∙
        ! (ap-∘
            (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀))
            (K₂-map (Loop2Grp-map-str (f , idp)))
            (loop (x₀ == x₀) x)))
        (ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀))
          (loop (x₀ == x₀) y) ∙
        ap (ap f) (K₂-rec-hom-β-pts x₀ idf2G y) ∙
        ! (K₂-rec-hom-β-pts y₀ idf2G (ap f y)) ∙
        ! (ap (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
            (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) y)) ∙
        ! (ap-∘
            (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀))
            (K₂-map (Loop2Grp-map-str (f , idp)))
            (loop (x₀ == x₀) y))) ◃∙
      ∙-assoc2-!-inv-l
        (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀) ∘ K₂-map (Loop2Grp-map-str (f , idp)))
        idp idp (loop (x₀ == x₀) x) (loop (x₀ == x₀) y) ◃∙
      ap (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀) ∘ K₂-map (Loop2Grp-map-str (f , idp))))
        (loop-comp (x₀ == x₀) x y) ◃∎
