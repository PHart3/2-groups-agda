{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import lib.FTID
open import lib.types.Pointed
open import lib.types.LoopSpace
open import 2GrpMap
open import Hmtpy2Grp
open import 2Magma
open import 2Grp

module LoopFunctor-ap where

open WkMagNatIso

-- move this function to lib.types.LoopSpace
Ω-fmap-ap-β : ∀ {i j} {X₁ : Ptd i} {X₂ : Ptd j} (f* : X₁ ⊙→ X₂) (x : _) → Ω-fmap-ap (⊙∼-id f*) x == idp
Ω-fmap-ap-β f*@(_ , idp) x = app= (⊙hom-ind-β f* (λ g* _ → Ω-fmap f* ∼ Ω-fmap g*) (λ _ → idp)) x

module _ {ℓ₁ ℓ₂} {X₁ : Ptd ℓ₁} {X₂ : Ptd ℓ₂} {{η₁ : has-level 2 (de⊙ X₁)}} {{η₂ : has-level 2 (de⊙ X₂)}} where

  Loop2Grp-map-ap : {f* g* : X₁ ⊙→ X₂} → f* ⊙-comp g* → CohGrpNatIso (Loop2Grp-map f*) (Loop2Grp-map g*)
  Loop2Grp-map-ap {f*} = 
    ⊙hom-ind f*
      (λ g* _ → CohGrpNatIso (Loop2Grp-map f*) (Loop2Grp-map g*))
      (natiso-id2G (Loop2Grp-map f*))
      
  Loop2Grp-map-ap-β : (f* : X₁ ⊙→ X₂) → Loop2Grp-map-ap (⊙∼-id f*) == natiso-id2G (Loop2Grp-map f*)
  Loop2Grp-map-ap-β f* =
    ⊙hom-ind-β f* (λ g* _ → CohGrpNatIso (Loop2Grp-map f*) (Loop2Grp-map g*)) (natiso-id2G (Loop2Grp-map f*))

  Loop2Grp-map-ap-fst : {f* g* : X₁ ⊙→ X₂} (H : f* ⊙-comp g*) → θ (Loop2Grp-map-ap H) ∼ Ω-fmap-ap H
  Loop2Grp-map-ap-fst {f*} =
    ⊙hom-ind f*
      (λ _ H → θ (Loop2Grp-map-ap H) ∼ Ω-fmap-ap H)
      (λ x → app= (ap θ (Loop2Grp-map-ap-β f*)) x ∙ ! (Ω-fmap-ap-β f* x))

  Ω-fmap-ap-pres : {f* g* : X₁ ⊙→ X₂} (H : f* ⊙-comp g*)
    → ap Loop2Grp-map (⊙-comp-to-== H) == natiso2G-to-== (Loop2Grp-map-ap H)
  Ω-fmap-ap-pres {f*} =
    ⊙hom-ind f*
      (λ g* H → ap Loop2Grp-map (⊙-comp-to-== H) == natiso2G-to-== (Loop2Grp-map-ap H))
      (ap (ap Loop2Grp-map) (⊙-comp-to-==-β f*) ∙
      ! (ap natiso2G-to-== (Loop2Grp-map-ap-β f*) ∙ natiso2G-to-==-β (Loop2Grp-map f*)))
