{-# OPTIONS --without-K --rewriting --lossy-unification --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import 2Semigroup
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import LoopK-hom
open import SqKLoop-aux4
open import SqKLoop-aux5
open import SqKLoop-aux6
open import SqKLoop-aux7
open import SqKLoop-aux8
open import SqKLoop-aux-defs1

module SqKLoop-aux9 where

module _ {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} (x₀ : X) (f : X → Y) where

  open Sq-aux6 x₀ f
  open Sq-aux8 x₀ f

  module _ (c₁ c₂ : base (x₀ == x₀) == base (x₀ == x₀))
    (ζ₃ :
      ap (fst (K₂-rec-hom y₀ idf2G)) (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁)
        ==
      ap f (ap (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₁))
    (ζ₄ :
      ap (fst (K₂-rec-hom y₀ idf2G)) (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₂)
        ==
      ap f (ap (fst (K₂-rec-hom x₀ idf2G)) c₂)) where

    open Sq-aux5 x₀ f c₁ c₂ ζ₃ ζ₄
    open Sq-aux7 x₀ f c₁ c₂

    abstract
      SqKLoop-coher4-aux3 :
        ! (
          ap2 _∙_
            (ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₁ ∙ ! ζ₃ ∙
              ! (ap-∘ (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)) (K₂-map (Loop2Grp-map-str (f , idp))) c₁))
            (ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₂ ∙ ! ζ₄ ∙
              ! (ap-∘ (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)) (K₂-map (Loop2Grp-map-str (f , idp))) c₂))) ◃∙
        ∙-ap (f ∘  K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₁ c₂ ◃∙
        ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) (c₁ ∙ c₂) ◃∙
        ap (ap f) (! (∙-ap (fst (K₂-rec-hom x₀ idf2G)) c₁ c₂ ∙ idp)) ◃∙
        ! (! (ap (λ z → z)
          (ap-∙ f (ap (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₁) (ap (fst (K₂-rec-hom x₀ idf2G)) c₂)))) ◃∙
        ! (ap2 _∙_ ζ₃ ζ₄) ◃∙
        ! (! (∙-ap (fst (K₂-rec-hom y₀ idf2G))
          (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁) (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₂) ∙ idp)) ◃∙
        ! (ap (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
          (! (∙-ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁ c₂))) ◃∙
        ! (ap-∘ (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)) (K₂-map (Loop2Grp-map-str (f , idp))) (c₁ ∙ c₂)) ◃∙
        idp ◃∎
          =ₛ
        ∙-assoc2-!-inv-l φ idp idp c₁ c₂ ◃∙
        idp ◃∎
      SqKLoop-coher4-aux3 =
        SqKLoop-coher4-aux3a x₀ f c₁ c₂ ζ₃ ζ₄ ∙ₛ
          (SqKLoop-coher4-aux3b ∙ₛ
            (SqKLoop-coher4-aux3c ∙ₛ
              (SqKLoop-coher4-aux3d ζ₃ ζ₄ ∙ₛ
                (SqKLoop-coher4-aux3e ζ₃ ζ₄ ∙ₛ
                  SqKLoop-coher4-aux3f c₁ c₂))))

    SqKLoop-coher4-aux2 :
      ∙-ap (f ∘ K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₁ c₂ ◃∙
      ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) (c₁ ∙ c₂) ◃∙
      ap (ap f) (! (∙-ap (fst (K₂-rec-hom x₀ idf2G)) c₁ c₂ ∙ idp)) ◃∙
      ! (! (ap (λ z → z)
        (ap-∙ f (ap (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₁) (ap (fst (K₂-rec-hom x₀ idf2G)) c₂)))) ◃∙
      ! (ap2 _∙_ ζ₃ ζ₄) ◃∙
      ! (! (∙-ap (fst (K₂-rec-hom y₀ idf2G))
        (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁) (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₂) ∙ idp)) ◃∙
      ! (ap (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
        (! (∙-ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁ c₂))) ◃∙
      ! (ap-∘ (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)) (K₂-map (Loop2Grp-map-str (f , idp))) (c₁ ∙ c₂)) ◃∙
      idp ◃∎
        =ₛ
      ap2 _∙_
        (ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₁ ∙ ! ζ₃ ∙
          ! (ap-∘ (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)) (K₂-map (Loop2Grp-map-str (f , idp))) c₁))
        (ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₂ ∙ ! ζ₄ ∙
          ! (ap-∘ (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)) (K₂-map (Loop2Grp-map-str (f , idp))) c₂)) ◃∙
      ∙-assoc2-!-inv-l φ idp idp c₁ c₂ ◃∙
      idp ◃∎
    SqKLoop-coher4-aux2 = pre-rotate'-out SqKLoop-coher4-aux3

  SqKLoop-coher4-aux : (c₁ c₂ {c₃} : base (x₀ == x₀) == base (x₀ == x₀)) (d₁ : c₁ ∙ c₂ == c₃)
    {e₁ e₂ e₃ : base (y₀ == y₀) == base (y₀ == y₀)}
    (ζ₅ : ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁ == e₁)
    (ζ₆ : ap (K₂-map (Loop2Grp-map-str (f , idp))) c₂ == e₂)
    (d₂ : e₁ ∙ e₂ == e₃)
    {x y : x₀ == x₀}
    (ζ₁ : ap (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₁ == x)
    (ζ₂ : ap (fst (K₂-rec-hom x₀ idf2G)) c₂ == y)
    (ζ₃ : ap (fst (K₂-rec-hom y₀ idf2G)) e₁ == ap f x) (ζ₄ : ap (fst (K₂-rec-hom y₀ idf2G)) e₂ == ap f y)
    →
    ∙-ap (f ∘ K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀))
      c₁ c₂ ∙
    ap (ap (f ∘ K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀))) d₁ ∙
    ! (ap (ap (f ∘ K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀))) d₁) ∙
    ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) (c₁ ∙ c₂) ∙
    ap (λ z → ap f (ap (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀ ) (loop-assoc' Λx₀)) z)) d₁ ∙
    ap (ap f)
      (! (∙-ap (fst (K₂-rec-hom x₀ idf2G)) c₁ c₂ ∙
         ap (ap (fst (K₂-rec-hom x₀ idf2G))) d₁)) ∙
    ap (ap f) (ap2 _∙_ ζ₁ ζ₂) ∙
    ! (! (ap (λ z → z) (ap-∙ f x y))) ∙
    ! (ap2 _∙_ ζ₃ ζ₄) ∙
    ! (!
        (∙-ap (fst (K₂-rec-hom y₀ idf2G)) e₁ e₂ ∙
        ap (ap (fst (K₂-rec-hom y₀ idf2G))) d₂)) ∙
    ! (ap
        (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀))) d₂) ∙
    ! (ap
        (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
        (ap2 _∙_ ζ₅ ζ₆)) ∙
    ! (ap
        (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
        (! (∙-ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁ c₂))) ∙
    ! (ap
        (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
        (! (ap (ap (K₂-map (Loop2Grp-map-str (f , idp)))) d₁))) ∙
    ! (ap (λ z → ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀))
      (ap (K₂-map (Loop2Grp-map-str (f , idp))) z)) d₁) ∙
    ! (ap-∘ (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)) (K₂-map (Loop2Grp-map-str (f , idp)))
      (c₁ ∙ c₂)) ∙
    ap (ap φ) d₁
      ==
    ap2 _∙_
      (ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₁ ∙
      ap (ap f) ζ₁ ∙
      ! ζ₃ ∙
      ! (ap (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀))) ζ₅) ∙
      ! (ap-∘
          (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀))
          (K₂-map (Loop2Grp-map-str (f , idp)))
          c₁))
      (ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₂ ∙
      ap (ap f) ζ₂ ∙
      ! ζ₄ ∙
      ! (ap (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀))) ζ₆) ∙
      ! (ap-∘
          (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀))
          (K₂-map (Loop2Grp-map-str (f , idp)))
          c₂)) ∙
    ∙-assoc2-!-inv-l φ idp idp c₁ c₂ ∙
    ap (ap φ) d₁
  SqKLoop-coher4-aux c₁ c₂ idp idp idp idp idp idp ζ₃ ζ₄ = =ₛ-out (SqKLoop-coher4-aux2 c₁ c₂ ζ₃ ζ₄)

  module _ (x y : x₀ == x₀) where

    open SqKLoop-abb1 x₀ f x y

    SqKLoop-coher4 : δ₃ =ₛ δ₄
    SqKLoop-coher4 = =ₛ-in $
       SqKLoop-coher4-aux (loop (x₀ == x₀) x) (loop (x₀ == x₀) y) (loop-comp (x₀ == x₀) x y)
         (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x)
         (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) y)
         (loop-comp (y₀ == y₀) (ap f x) (ap f y))
         (K₂-rec-hom-β-pts x₀ idf2G x)
         (K₂-rec-hom-β-pts x₀ idf2G y)
         (K₂-rec-hom-β-pts y₀ idf2G (ap f x))
         (K₂-rec-hom-β-pts y₀ idf2G (ap f y))

