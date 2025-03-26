{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.LoopSpace
open import 2Grp
open import 2Magma
open import 2MagMap
open import 2GrpMap
open import 2GrpMap-conv
open import Hmtpy2Grp
open import NatIso
open import 2GrpMap-conv
open import LoopFunctor
open import LoopFunctor-ap

module LoopFunctor-conv where

open CohGrp {{...}}
open WkMagNatIso

module _ {ℓ₁ ℓ₂} {X₁ : Ptd ℓ₁} {X₂ : Ptd ℓ₂} {{η₁ : has-level 2 (de⊙ X₁)}} {{η₂ : has-level 2 (de⊙ X₂)}} where

  abstract

    Ω-ρ : (f* : X₁ ⊙→ X₂) →
      ap Loop2Grp-map (⊙-comp-to-== (⊙∘-runit f*)) ∙
      natiso2G-to-== (Loop2Grp-map-∘ f* (⊙idf X₁)) ∙
      ap (λ m → Loop2Grp-map {{η₁}} {{η₂}} f* ∘2G m) (natiso2G-to-== (Loop2Grp-map-idf X₁))
        ==
      natiso2G-to-== (unit-wkmaghom-r (grphom-forg (Loop2Grp-map f*))) 
    Ω-ρ f* = =ₛ-out $
      ap Loop2Grp-map (⊙-comp-to-== (⊙∘-runit f*)) ◃∙
      natiso2G-to-== (Loop2Grp-map-∘ f* (⊙idf X₁)) ◃∙
      ap (λ m → Loop2Grp-map {{η₁}} {{η₂}} f* ∘2G m) (natiso2G-to-== (Loop2Grp-map-idf X₁)) ◃∎
        =ₛ₁⟨ 0 & 1 & Ω-fmap-ap-pres (⊙∘-runit f*) ⟩
      natiso2G-to-== (Loop2Grp-map-ap (⊙∘-runit f*)) ◃∙
      natiso2G-to-== (Loop2Grp-map-∘ f* (⊙idf X₁)) ◃∙
      ap (λ m → Loop2Grp-map {{η₁}} {{η₂}} f* ∘2G m) (natiso2G-to-== (Loop2Grp-map-idf X₁)) ◃∎
        =ₛ₁⟨ 2 & 1 & ! (whisk2G-conv-l (Loop2Grp-map-idf X₁)) ⟩
      natiso2G-to-== (Loop2Grp-map-ap (⊙∘-runit f*)) ◃∙
      natiso2G-to-== (Loop2Grp-map-∘ f* (⊙idf X₁)) ◃∙
      natiso2G-to-== (natiso-whisk-l (Loop2Grp-map-idf X₁)) ◃∎
        =ₛ⟨ !ₛ (∘2G-conv-tri (Loop2Grp-map-ap (⊙∘-runit f*)) (Loop2Grp-map-∘ f* (⊙idf X₁)) (natiso-whisk-l (Loop2Grp-map-idf X₁))) ⟩
      natiso2G-to-== (natiso-whisk-l (Loop2Grp-map-idf X₁) natiso-∘ Loop2Grp-map-∘ f* (⊙idf X₁) natiso-∘ Loop2Grp-map-ap (⊙∘-runit f*)) ◃∎
        =ₛ₁⟨ ap natiso2G-to-==
               (natiso∼-to-== (λ p →
                 ∙-assoc (θ (Loop2Grp-map-ap (⊙∘-runit f*)) p) (θ (Loop2Grp-map-∘ f* (⊙idf X₁)) p) (ap (Ω-fmap f*) (ap-idf p)) ∙
                 =ₛ-out (Loop2Grp-map-runit f* p))) ⟩
      natiso2G-to-== (unit-wkmaghom-r (grphom-forg (Loop2Grp-map f*))) ◃∎ ∎ₛ
