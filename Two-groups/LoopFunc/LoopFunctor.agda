{-# OPTIONS --without-K --rewriting --overlapping-instances --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.LoopSpace
open import 2Magma
open import 2Grp
open import Hmtpy2Grp

-- pseudofunctorial properties of Ω

module LoopFunctor where

open WkMagNatIso

module _ {ℓ₁ ℓ₂} {X₁ : Ptd ℓ₁} {X₂ : Ptd ℓ₂} {{η₁ : has-level 2 (de⊙ X₁)}} {{η₂ : has-level 2 (de⊙ X₂)}} where

  abstract

    Loop2Grp-map-runit : (f* : X₁ ⊙→ X₂) (p : Ω X₁) →
      Ω-fmap-ap (⊙∘-runit f*) p ◃∙
      θ (Loop2Grp-map-∘ f* (⊙idf X₁)) p ◃∙
      ap (Ω-fmap f*) (ap-idf p) ◃∎
        =ₛ
      idp ◃∎
    Loop2Grp-map-runit (f , idp) p =
      ⊙hom-ind (f , idp) (λ g* _ → ap f ∼ Ω-fmap g*) (λ x → idp) (⊙∘-runit (f , idp)) p ◃∙
      ap-∘ f (λ z → z) p ◃∙
      ap (ap f) (ap-idf p) ◃∎
        =ₛ₁⟨ 0 & 1 & app= (⊙hom-ind-β (f , idp) (λ g* _ → ap f ∼ Ω-fmap g*) (λ x → idp)) p ⟩
      idp ◃∙
      ap-∘ f (λ z → z) p ◃∙
      ap (ap f) (ap-idf p) ◃∎
        =ₛ₁⟨ aux p ⟩
      idp ◃∎ ∎ₛ
        where
          aux : {x y : de⊙ X₁} (p : x == y) → ap-∘ f (λ z → z) p ∙ ap (ap f) (ap-idf p) == idp
          aux idp = idp

    Loop2Grp-map-lunit : (f* : X₁ ⊙→ X₂) (p : Ω X₁) →
      Ω-fmap-ap (⊙∘-lunit f*) p ◃∙
      θ (Loop2Grp-map-∘ (⊙idf X₂) f*) p ◃∙
      ap-idf (Ω-fmap f* p) ◃∎
        =ₛ
      idp ◃∎
    Loop2Grp-map-lunit (f , idp) p =
      ⊙hom-ind (f , idp) (λ g* _ → ap f ∼ Ω-fmap g*) (λ x → idp) (⊙∘-lunit (f , idp)) p ◃∙
      ap-∘ (λ z → z) f p ◃∙
      ap-idf (ap f p) ◃∎
        =ₛ₁⟨ 0 & 1 & app= (⊙hom-ind-β (f , idp) (λ g* _ → ap f ∼ Ω-fmap g*) (λ x → idp)) p ⟩
      idp ◃∙
      ap-∘ (λ z → z) f p ◃∙
      ap-idf (ap f p) ◃∎
        =ₛ₁⟨ aux p ⟩
      idp ◃∎ ∎ₛ
        where
          aux : {x y : de⊙ X₁} (p : x == y) → ap-∘  (λ z → z) f p ∙ ap-idf (ap f p) == idp
          aux idp = idp
    
module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {X₁ : Ptd ℓ₁} {X₂ : Ptd ℓ₂} {X₃ : Ptd ℓ₃} {X₄ : Ptd ℓ₄}
  {{η₁ : has-level 2 (de⊙ X₁)}} {{η₂ : has-level 2 (de⊙ X₂)}} {{η₃ : has-level 2 (de⊙ X₃)}} {{η₄ : has-level 2 (de⊙ X₄)}} where

  abstract
    Loop2Grp-map-assoc : (f₁* : X₁ ⊙→ X₂) (f₂* : X₂ ⊙→ X₃) (f₃* : X₃ ⊙→ X₄) (p : Ω X₁) →
      ! (ap (Ω-fmap f₃*) (θ (Loop2Grp-map-∘ f₂* f₁*) p)) ◃∙
      ! (θ (Loop2Grp-map-∘ f₃* (f₂* ⊙∘ f₁*)) p) ◃∙
      Ω-fmap-ap (⊙∘-α-comp f₃* f₂* f₁*) p ◃∙
      θ (Loop2Grp-map-∘ (f₃* ⊙∘ f₂*) f₁*) p ◃∙
      θ (Loop2Grp-map-∘ f₃* f₂*) (Ω-fmap f₁* p) ◃∎
        =ₛ
      idp ◃∎
    Loop2Grp-map-assoc (f₁ , idp) (f₂ , idp) (f₃ , idp) p =
      ! (ap (ap f₃) (ap-∘ f₂ f₁ p)) ◃∙
      ! (ap-∘ f₃ (f₂ ∘ f₁) p) ◃∙
      ⊙hom-ind (f₃ ∘ f₂ ∘ f₁ , idp)
        (λ g* _ → ap (f₃ ∘ f₂ ∘ f₁) ∼ Ω-fmap g*) (λ x → idp) (⊙∘-α-comp (f₃ , idp) (f₂ , idp) (f₁ , idp)) p ◃∙
      ap-∘ (f₃ ∘ f₂) f₁ p ◃∙
      ap-∘ f₃ f₂ (ap f₁ p) ◃∎
        =ₛ₁⟨ 2 & 1 & app= (⊙hom-ind-β (f₃ ∘ f₂ ∘ f₁ , idp) (λ g* _ → ap (f₃ ∘ f₂ ∘ f₁) ∼ Ω-fmap g*) (λ x → idp)) p ⟩
      ! (ap (ap f₃) (ap-∘ f₂ f₁ p)) ◃∙
      ! (ap-∘ f₃ (f₂ ∘ f₁) p) ◃∙
      idp ◃∙
      ap-∘ (f₃ ∘ f₂) f₁ p ◃∙
      ap-∘ f₃ f₂ (ap f₁ p) ◃∎
        =ₛ₁⟨ aux p ⟩
      idp ◃∎ ∎ₛ
        where
          aux : {x y : de⊙ X₁} (p : x == y) →
            ! (ap (ap f₃) (ap-∘ f₂ f₁ p)) ∙
            ! (ap-∘ f₃ (f₂ ∘ f₁) p) ∙
            ap-∘ (f₃ ∘ f₂) f₁ p ∙
            ap-∘ f₃ f₂ (ap f₁ p)
              ==
            idp
          aux idp = idp
