{-# OPTIONS --without-K --rewriting --lossy-unification --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import LoopK

module SqKLoop-aux-defs2 where

module _ {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} (x₀ : X) (f : X → Y) where

  private
    y₀ = f x₀
    Λx₀ = wkmag-to-loop x₀ (cohmaghom (idf (x₀ == x₀)) {{idf2G}})
    Λy₀ = wkmag-to-loop y₀ (cohmaghom (idf (y₀ == y₀)) {{idf2G}})

  module SqKLoop-abb2 (c₁ c₂ : base (x₀ == x₀) == base (x₀ == x₀))
    (ζ₃ :
      ap (fst (K₂-rec-hom y₀ idf2G)) (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁)
        ==
      ap f (ap (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₁))
    (ζ₄ :
      ap (fst (K₂-rec-hom y₀ idf2G)) (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₂)
        ==
      ap f (ap (fst (K₂-rec-hom x₀ idf2G)) c₂)) where

    private
      h₀ =
        ! (ap (_∙_
            (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀) ∘ K₂-map (Loop2Grp-map-str (f , idp))) c₁))
        (ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₂ ∙ ! ζ₄ ∙
        ! (ap-∘ (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)) (K₂-map (Loop2Grp-map-str (f , idp))) c₂)))

    ξ₁ =
      h₀ ◃∙
      ! (ap (λ u → u ∙ ap (f ∘  K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₂)
          (ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₁ ∙ ! ζ₃ ∙
          ! (ap-∘ (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)) (K₂-map (Loop2Grp-map-str (f , idp))) c₁))) ◃∙
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

    ξ₂ = 
      h₀ ◃∙
      ! (ap (λ u → u ∙ ap (f ∘  K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₂)
          (ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₁ ∙ ! ζ₃ ∙
          ! (ap-∘ (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)) (K₂-map (Loop2Grp-map-str (f , idp))) c₁))) ◃∙
      ∙-ap (f ∘  K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₁ c₂ ◃∙
      ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) (c₁ ∙ c₂) ◃∙
      ap (ap f) (! (∙-ap (fst (K₂-rec-hom x₀ idf2G)) c₁ c₂ ∙ idp)) ◃∙
      ! (! (ap (λ z → z)
        (ap-∙ f (ap (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₁) (ap (fst (K₂-rec-hom x₀ idf2G)) c₂)))) ◃∙
      ! (ap (λ u → u ∙ ap f (ap (fst (K₂-rec-hom x₀ idf2G)) c₂)) ζ₃) ◃∙
      ! (ap (_∙_ (ap (fst (K₂-rec-hom y₀ idf2G)) (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁))) ζ₄) ◃∙
      ! (! (∙-ap (fst (K₂-rec-hom y₀ idf2G))
        (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁) (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₂) ∙ idp)) ◃∙
      ! (ap (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
        (! (∙-ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁ c₂))) ◃∙
      ! (ap-∘ (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)) (K₂-map (Loop2Grp-map-str (f , idp))) (c₁ ∙ c₂)) ◃∙
      idp ◃∎

    h₁ =
      ! (ap (_∙_
          (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀) ∘ K₂-map (Loop2Grp-map-str (f , idp))) c₁))
        (! (ap-∘ (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)) (K₂-map (Loop2Grp-map-str (f , idp))) c₂)))
    h₂ =
      ! (ap (_∙_
          (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀) ∘ K₂-map (Loop2Grp-map-str (f , idp))) c₁)) (! ζ₄))
    h₃ =
      ! (ap (_∙_
          (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀) ∘ K₂-map (Loop2Grp-map-str (f , idp))) c₁))
        (ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₂))

    ξ₃ =
      h₁ ◃∙
      h₂ ◃∙
      h₃ ◃∙
      ! (ap (λ u → u ∙ ap (f ∘  K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₂)
          (ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₁ ∙ ! ζ₃ ∙
          ! (ap-∘ (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)) (K₂-map (Loop2Grp-map-str (f , idp))) c₁))) ◃∙
      ∙-ap (f ∘  K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₁ c₂ ◃∙
      ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) (c₁ ∙ c₂) ◃∙
      ap (ap f) (! (∙-ap (fst (K₂-rec-hom x₀ idf2G)) c₁ c₂ ∙ idp)) ◃∙
      ! (! (ap (λ z → z)
        (ap-∙ f (ap (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₁) (ap (fst (K₂-rec-hom x₀ idf2G)) c₂)))) ◃∙
      ! (ap (λ u → u ∙ ap f (ap (fst (K₂-rec-hom x₀ idf2G)) c₂)) ζ₃) ◃∙
      ! (ap (_∙_ (ap (fst (K₂-rec-hom y₀ idf2G)) (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁))) ζ₄) ◃∙
      ! (! (∙-ap (fst (K₂-rec-hom y₀ idf2G))
        (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁) (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₂) ∙ idp)) ◃∙
      ! (ap (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
        (! (∙-ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁ c₂))) ◃∙
      ! (ap-∘ (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)) (K₂-map (Loop2Grp-map-str (f , idp))) (c₁ ∙ c₂)) ◃∙
      idp ◃∎

    ξ₄ = 
      h₁ ◃∙
      h₂ ◃∙
      h₃ ◃∙
      ! (ap (λ u → u ∙ ap (f ∘  K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₂)
           (! (ap-∘ (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)) (K₂-map (Loop2Grp-map-str (f , idp))) c₁))) ◃∙
      ! (ap (λ u → u ∙ ap (f ∘  K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₂) (! ζ₃)) ◃∙
      ! (ap (λ u → u ∙ ap (f ∘  K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₂)
          (ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₁)) ◃∙
      ∙-ap (f ∘  K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₁ c₂ ◃∙
      ap-∘ f (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) (c₁ ∙ c₂) ◃∙
      ap (ap f) (! (∙-ap (fst (K₂-rec-hom x₀ idf2G)) c₁ c₂ ∙ idp)) ◃∙
      ! (! (ap (λ z → z)
        (ap-∙ f (ap (K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)) c₁) (ap (fst (K₂-rec-hom x₀ idf2G)) c₂)))) ◃∙
      ! (ap (λ u → u ∙ ap f (ap (fst (K₂-rec-hom x₀ idf2G)) c₂)) ζ₃) ◃∙
      ! (ap (_∙_ (ap (fst (K₂-rec-hom y₀ idf2G)) (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁))) ζ₄) ◃∙
      ! (! (∙-ap (fst (K₂-rec-hom y₀ idf2G))
        (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁) (ap (K₂-map (Loop2Grp-map-str (f , idp))) c₂) ∙ idp)) ◃∙
      ! (ap (ap (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)))
        (! (∙-ap (K₂-map (Loop2Grp-map-str (f , idp))) c₁ c₂))) ◃∙
      ! (ap-∘ (K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)) (K₂-map (Loop2Grp-map-str (f , idp))) (c₁ ∙ c₂)) ◃∙
      idp ◃∎
