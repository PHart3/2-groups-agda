{-# OPTIONS --without-K --rewriting --lossy-unification --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import 2Semigroup
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import LoopK-hom
open import SqKLoop-aux1-defs

module SqKLoop-aux1 where

module _ {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} (x₀ : X)
  (f : X → Y) (x y : x₀ == x₀) where

  open SqKLoop-aux1-abb x₀ f x y
  
  SqKLoop-coher1 = 
    ∙-ap (f ∘ K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀))
      (loop (x₀ == x₀) x) (loop (x₀ == x₀) y) ◃∙
    ap (ap (f ∘ K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)))
      (loop-comp (x₀ == x₀) x y) ◃∙
    (ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀))
      (loop (x₀ == x₀) (x ∙ y)) ∙
    ap (ap f) (K₂-rec-hom-β-pts x₀ idf2G (x ∙ y)) ∙
    ! (K₂-rec-hom-β-pts y₀ idf2G (ap f (x ∙ y))) ∙
    ! (ap (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
        (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) (x ∙ y))) ∙
    ! (ap-∘ (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)) (K₂-map (Loop2Grp-map-str (f , idp)))
        (loop (x₀ == x₀) (x ∙ y)))) ◃∎
      =ₛ⟨ =ₛ-in $
            ap (λ p →
              ∙-ap (f ∘ K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀))
                (loop (x₀ == x₀) x) (loop (x₀ == x₀) y) ∙
              ap (ap (f ∘ K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)))
                (loop-comp (x₀ == x₀) x y) ∙
              p) idp ⟩
    ν₁
      =ₛ⟨ 3 & 1 & ap-seq-=ₛ (ap f) (K₂-rec-hom-β-comp x₀ idf2G x y) ⟩
    ν₂
      =ₛ⟨ 7 & 1 & 
        !-=ₛ
          (ap-seq-=ₛ
            (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
            (K₂-map-β-comp (Loop2Grp-map-str (f , idp)) x y)) ⟩
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
    ! (K₂-rec-hom-β-pts y₀ idf2G (ap f (x ∙ y))) ◃∙
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
        (loop (x₀ == x₀) (x ∙ y))) ◃∎ ∎ₛ
