{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.LoopSpace
open import 2Grp
open import 2Semigroup
open import 2SGrpMap
open import 2GrpMap
open import 2GrpMap-conv
open import Hmtpy2Grp
open import NatIso
open import 2GrpMap-conv
open import LoopFunctor-coher
open import LoopFunctor-ap

-- conversion of pseudofunctorial properties of Ω to ==

module LoopFunctor-conv where

open CohGrp {{...}}
open WkSGrpNatIso

module _ {ℓ₁ ℓ₂} {X₁ : Ptd ℓ₁} {X₂ : Ptd ℓ₂} {{η₁ : has-level 2 (de⊙ X₁)}} {{η₂ : has-level 2 (de⊙ X₂)}}
  (f* : X₁ ⊙→ X₂) where

  abstract

    Ω-ρ :
      ap Loop2Grp-map (⊙-comp-to-== (⊙∘-runit f*)) ∙
      natiso2G-to-== (Loop2Grp-map-∘ f* (⊙idf X₁)) ∙
      ap (λ m → Loop2Grp-map {{η₁}} {{η₂}} f* ∘2G m) (natiso2G-to-== (Loop2Grp-map-idf X₁))
        ==
      natiso2G-to-== (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f*))) 
    Ω-ρ = =ₛ-out $
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
      natiso2G-to-==
        (natiso-whisk-l (Loop2Grp-map-idf X₁) natiso-∘ Loop2Grp-map-∘ f* (⊙idf X₁) natiso-∘ Loop2Grp-map-ap (⊙∘-runit f*)) ◃∎
        =ₛ₁⟨ ap natiso2G-to-==
               (natiso∼-to-== (λ p →
                 ∙-assoc (θ (Loop2Grp-map-ap (⊙∘-runit f*)) p) (θ (Loop2Grp-map-∘ f* (⊙idf X₁)) p) (ap (Ω-fmap f*) (ap-idf p)) ∙
                 =ₛ-out (Loop2Grp-map-runit f* p))) ⟩
      natiso2G-to-== (unit-wksgrphom-r (grphom-forg (Loop2Grp-map f*))) ◃∎ ∎ₛ

    Ω-λ :
      ap Loop2Grp-map (⊙-comp-to-== (⊙∘-lunit f*)) ∙
      natiso2G-to-== (Loop2Grp-map-∘ (⊙idf X₂) f*) ∙
      ap (λ m → m ∘2G Loop2Grp-map {{η₁}} {{η₂}} f*) (natiso2G-to-== (Loop2Grp-map-idf X₂))
        ==
      natiso2G-to-== (unit-wksgrphom-l (grphom-forg (Loop2Grp-map f*)))
    Ω-λ = =ₛ-out $
      ap Loop2Grp-map (⊙-comp-to-== (⊙∘-lunit f*)) ◃∙
      natiso2G-to-== (Loop2Grp-map-∘ (⊙idf X₂) f*) ◃∙
      ap (λ m → m ∘2G Loop2Grp-map {{η₁}} {{η₂}} f*) (natiso2G-to-== (Loop2Grp-map-idf X₂)) ◃∎
        =ₛ₁⟨ 0 & 1 & Ω-fmap-ap-pres (⊙∘-lunit f*) ⟩
      natiso2G-to-== (Loop2Grp-map-ap (⊙∘-lunit f*)) ◃∙
      natiso2G-to-== (Loop2Grp-map-∘ (⊙idf X₂) f*) ◃∙
      ap (λ m → m ∘2G Loop2Grp-map {{η₁}} {{η₂}} f*) (natiso2G-to-== (Loop2Grp-map-idf X₂)) ◃∎
        =ₛ₁⟨ 2 & 1 & ! (whisk2G-conv-r (Loop2Grp-map-idf X₂)) ⟩
      natiso2G-to-== (Loop2Grp-map-ap (⊙∘-lunit f*)) ◃∙
      natiso2G-to-== (Loop2Grp-map-∘ (⊙idf X₂) f*) ◃∙
      natiso2G-to-== (natiso-whisk-r (Loop2Grp-map-idf X₂)) ◃∎
        =ₛ⟨ !ₛ (∘2G-conv-tri (Loop2Grp-map-ap (⊙∘-lunit f*)) (Loop2Grp-map-∘ (⊙idf X₂) f*) (natiso-whisk-r (Loop2Grp-map-idf X₂))) ⟩
      natiso2G-to-==
        (natiso-whisk-r (Loop2Grp-map-idf X₂) natiso-∘ Loop2Grp-map-∘ (⊙idf X₂) f* natiso-∘ Loop2Grp-map-ap (⊙∘-lunit f*)) ◃∎
        =ₛ₁⟨ ap natiso2G-to-==
               (natiso∼-to-== (λ p →
                 ∙-assoc (θ (Loop2Grp-map-ap (⊙∘-lunit f*)) p) (θ (Loop2Grp-map-∘ (⊙idf X₂) f*) p) (ap-idf (Ω-fmap f* p)) ∙
                 =ₛ-out (Loop2Grp-map-lunit f* p))) ⟩
      natiso2G-to-== (unit-wksgrphom-l (grphom-forg (Loop2Grp-map f*))) ◃∎ ∎ₛ

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {X₁ : Ptd ℓ₁} {X₂ : Ptd ℓ₂} {X₃ : Ptd ℓ₃} {X₄ : Ptd ℓ₄}
  {{η₁ : has-level 2 (de⊙ X₁)}} {{η₂ : has-level 2 (de⊙ X₂)}} {{η₃ : has-level 2 (de⊙ X₃)}} {{η₄ : has-level 2 (de⊙ X₄)}} where

  abstract
    Ω-α : (f₃* : X₃ ⊙→ X₄) (f₂* : X₂ ⊙→ X₃) (f₁* : X₁ ⊙→ X₂) →
      ! (ap (λ m → Loop2Grp-map {{η₃}} {{η₄}} f₃* ∘2G m) (natiso2G-to-== (Loop2Grp-map-∘ f₂* f₁*))) ∙
      ! (natiso2G-to-== (Loop2Grp-map-∘ f₃* (f₂* ⊙∘ f₁*))) ∙
      ap Loop2Grp-map (⊙-comp-to-== (⊙∘-α-comp f₃* f₂* f₁*)) ∙
      natiso2G-to-== (Loop2Grp-map-∘ (f₃* ⊙∘ f₂*) f₁*) ∙
      ap (λ m → m ∘2G Loop2Grp-map f₁*) (natiso2G-to-== (Loop2Grp-map-∘ f₃* f₂*))
        ==
      natiso2G-to-==
        (assoc-wksgrphom (grphom-forg (Loop2Grp-map f₃*)) (grphom-forg (Loop2Grp-map f₂*)) (grphom-forg (Loop2Grp-map f₁*)))
    Ω-α f₃* f₂* f₁* = =ₛ-out $
      ! (ap (λ m → Loop2Grp-map f₃* ∘2G m) (natiso2G-to-== (Loop2Grp-map-∘ f₂* f₁*))) ◃∙
      ! (natiso2G-to-== (Loop2Grp-map-∘ f₃* (f₂* ⊙∘ f₁*))) ◃∙
      ap Loop2Grp-map (⊙-comp-to-== (⊙∘-α-comp f₃* f₂* f₁*)) ◃∙
      natiso2G-to-== (Loop2Grp-map-∘ (f₃* ⊙∘ f₂*) f₁*) ◃∙
      ap (λ m → m ∘2G Loop2Grp-map f₁*) (natiso2G-to-== (Loop2Grp-map-∘ f₃* f₂*)) ◃∎
        =ₛ₁⟨ 0 & 1 & ap ! (! (whisk2G-conv-l (Loop2Grp-map-∘ f₂* f₁*))) ⟩
      ! (natiso2G-to-== (natiso-whisk-l (Loop2Grp-map-∘ f₂* f₁*))) ◃∙
      ! (natiso2G-to-== (Loop2Grp-map-∘ f₃* (f₂* ⊙∘ f₁*))) ◃∙
      ap Loop2Grp-map (⊙-comp-to-== (⊙∘-α-comp f₃* f₂* f₁*)) ◃∙
      natiso2G-to-== (Loop2Grp-map-∘ (f₃* ⊙∘ f₂*) f₁*) ◃∙
      ap (λ m → m ∘2G Loop2Grp-map f₁*) (natiso2G-to-== (Loop2Grp-map-∘ f₃* f₂*)) ◃∎
        =ₛ₁⟨ 0 & 1 & ! (natiso2G-! (natiso-whisk-l (Loop2Grp-map-∘ f₂* f₁*))) ⟩
      natiso2G-to-== (!ʷ (natiso-whisk-l (Loop2Grp-map-∘ f₂* f₁*))) ◃∙
      ! (natiso2G-to-== (Loop2Grp-map-∘ f₃* (f₂* ⊙∘ f₁*))) ◃∙
      ap Loop2Grp-map (⊙-comp-to-== (⊙∘-α-comp f₃* f₂* f₁*)) ◃∙
      natiso2G-to-== (Loop2Grp-map-∘ (f₃* ⊙∘ f₂*) f₁*) ◃∙
      ap (λ m → m ∘2G Loop2Grp-map f₁*) (natiso2G-to-== (Loop2Grp-map-∘ f₃* f₂*)) ◃∎
        =ₛ₁⟨ 1 & 1 & ! (natiso2G-! (Loop2Grp-map-∘ f₃* (f₂* ⊙∘ f₁*))) ⟩
      natiso2G-to-== (!ʷ (natiso-whisk-l (Loop2Grp-map-∘ f₂* f₁*))) ◃∙
      natiso2G-to-== (!ʷ (Loop2Grp-map-∘ f₃* (f₂* ⊙∘ f₁*))) ◃∙
      ap Loop2Grp-map (⊙-comp-to-== (⊙∘-α-comp f₃* f₂* f₁*)) ◃∙
      natiso2G-to-== (Loop2Grp-map-∘ (f₃* ⊙∘ f₂*) f₁*) ◃∙
      ap (λ m → m ∘2G Loop2Grp-map f₁*) (natiso2G-to-== (Loop2Grp-map-∘ f₃* f₂*)) ◃∎
        =ₛ₁⟨ 2 & 1 & Ω-fmap-ap-pres (⊙∘-α-comp f₃* f₂* f₁*) ⟩
      natiso2G-to-== (!ʷ (natiso-whisk-l (Loop2Grp-map-∘ f₂* f₁*))) ◃∙
      natiso2G-to-== (!ʷ (Loop2Grp-map-∘ f₃* (f₂* ⊙∘ f₁*))) ◃∙
      natiso2G-to-== (Loop2Grp-map-ap (⊙∘-α-comp f₃* f₂* f₁*)) ◃∙
      natiso2G-to-== (Loop2Grp-map-∘ (f₃* ⊙∘ f₂*) f₁*) ◃∙
      ap (λ m → m ∘2G Loop2Grp-map f₁*) (natiso2G-to-== (Loop2Grp-map-∘ f₃* f₂*)) ◃∎
        =ₛ₁⟨ 4 & 1 & ! (whisk2G-conv-r (Loop2Grp-map-∘ f₃* f₂*)) ⟩
      natiso2G-to-== (!ʷ (natiso-whisk-l (Loop2Grp-map-∘ f₂* f₁*))) ◃∙
      natiso2G-to-== (!ʷ (Loop2Grp-map-∘ f₃* (f₂* ⊙∘ f₁*))) ◃∙
      natiso2G-to-== (Loop2Grp-map-ap (⊙∘-α-comp f₃* f₂* f₁*)) ◃∙
      natiso2G-to-== (Loop2Grp-map-∘ (f₃* ⊙∘ f₂*) f₁*) ◃∙
      natiso2G-to-== (natiso-whisk-r (Loop2Grp-map-∘ f₃* f₂*)) ◃∎
        =ₛ⟨ ∘2G-conv-quint
              (!ʷ (natiso-whisk-l (Loop2Grp-map-∘ f₂* f₁*)))
              (!ʷ (Loop2Grp-map-∘ f₃* (f₂* ⊙∘ f₁*)))
              (Loop2Grp-map-ap (⊙∘-α-comp f₃* f₂* f₁*))
              (Loop2Grp-map-∘ (f₃* ⊙∘ f₂*) f₁*)
              (natiso-whisk-r (Loop2Grp-map-∘ f₃* f₂*)) ⟩
      natiso2G-to-==
        (natiso-whisk-r (Loop2Grp-map-∘ f₃* f₂*) natiso-∘
        Loop2Grp-map-∘ (f₃* ⊙∘ f₂*) f₁* natiso-∘
        Loop2Grp-map-ap (⊙∘-α-comp f₃* f₂* f₁*) natiso-∘
        !ʷ (Loop2Grp-map-∘ f₃* (f₂* ⊙∘ f₁*)) natiso-∘
        !ʷ (natiso-whisk-l (Loop2Grp-map-∘ f₂* f₁*))) ◃∎
        =ₛ₁⟨ ap natiso2G-to-== (
               natiso∼-to-== (λ p → ! (=ₛ-out (re-associate p)) ∙ =ₛ-out (Loop2Grp-map-assoc f₁* f₂* f₃* p))) ⟩
      natiso2G-to-==
        (assoc-wksgrphom (grphom-forg (Loop2Grp-map f₃*)) (grphom-forg (Loop2Grp-map f₂*)) (grphom-forg (Loop2Grp-map f₁*))) ◃∎ ∎ₛ
        where abstract
          re-associate : (p : _) →
            ! (ap (Ω-fmap f₃*) (θ (Loop2Grp-map-∘ f₂* f₁*) p)) ◃∙
            ! (θ (Loop2Grp-map-∘ f₃* (f₂* ⊙∘ f₁*)) p) ◃∙
            θ (Loop2Grp-map-ap (⊙∘-α-comp f₃* f₂* f₁*)) p ◃∙
            θ (Loop2Grp-map-∘ (f₃* ⊙∘ f₂*) f₁*) p ◃∙
            θ (Loop2Grp-map-∘ f₃* f₂*) (Ω-fmap f₁* p) ◃∎
              =ₛ
            (((! (ap (Ω-fmap f₃*) (θ (Loop2Grp-map-∘ f₂* f₁*) p)) ∙
                 ! (θ (Loop2Grp-map-∘ f₃* (f₂* ⊙∘ f₁*)) p)) ∙
               θ (Loop2Grp-map-ap (⊙∘-α-comp f₃* f₂* f₁*)) p) ∙
              θ (Loop2Grp-map-∘ (f₃* ⊙∘ f₂*) f₁*) p) ◃∙
             θ (Loop2Grp-map-∘ f₃* f₂*) (Ω-fmap f₁* p) ◃∎
          re-associate p =
            ! (ap (Ω-fmap f₃*) (θ (Loop2Grp-map-∘ f₂* f₁*) p)) ◃∙
            ! (θ (Loop2Grp-map-∘ f₃* (f₂* ⊙∘ f₁*)) p) ◃∙
            θ (Loop2Grp-map-ap (⊙∘-α-comp f₃* f₂* f₁*)) p ◃∙
            θ (Loop2Grp-map-∘ (f₃* ⊙∘ f₂*) f₁*) p ◃∙
            θ (Loop2Grp-map-∘ f₃* f₂*) (Ω-fmap f₁* p) ◃∎
              =ₛ₁⟨ 0 & 2 & idp ⟩
            (! (ap (Ω-fmap f₃*) (θ (Loop2Grp-map-∘ f₂* f₁*) p)) ∙
            ! (θ (Loop2Grp-map-∘ f₃* (f₂* ⊙∘ f₁*)) p)) ◃∙
            θ (Loop2Grp-map-ap (⊙∘-α-comp f₃* f₂* f₁*)) p ◃∙
            θ (Loop2Grp-map-∘ (f₃* ⊙∘ f₂*) f₁*) p ◃∙
            θ (Loop2Grp-map-∘ f₃* f₂*) (Ω-fmap f₁* p) ◃∎
              =ₛ₁⟨ 0 & 2 & idp ⟩
            ((! (ap (Ω-fmap f₃*) (θ (Loop2Grp-map-∘ f₂* f₁*) p)) ∙
            ! (θ (Loop2Grp-map-∘ f₃* (f₂* ⊙∘ f₁*)) p)) ∙
            θ (Loop2Grp-map-ap (⊙∘-α-comp f₃* f₂* f₁*)) p) ◃∙
            θ (Loop2Grp-map-∘ (f₃* ⊙∘ f₂*) f₁*) p ◃∙
            θ (Loop2Grp-map-∘ f₃* f₂*) (Ω-fmap f₁* p) ◃∎
              =ₛ₁⟨ 0 & 2 & idp ⟩
            (((! (ap (Ω-fmap f₃*) (θ (Loop2Grp-map-∘ f₂* f₁*) p)) ∙
                 ! (θ (Loop2Grp-map-∘ f₃* (f₂* ⊙∘ f₁*)) p)) ∙
               θ (Loop2Grp-map-ap (⊙∘-α-comp f₃* f₂* f₁*)) p) ∙
              θ (Loop2Grp-map-∘ (f₃* ⊙∘ f₂*) f₁*) p) ◃∙
             θ (Loop2Grp-map-∘ f₃* f₂*) (Ω-fmap f₁* p) ◃∎ ∎ₛ
