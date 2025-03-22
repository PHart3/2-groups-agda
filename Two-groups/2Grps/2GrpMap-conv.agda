{-# OPTIONS --without-K --rewriting --overlapping-instances --lossy-unification #-}

open import lib.Basics
open import 2Magma
open import 2MagMap
open import 2Grp
open import 2GrpMap
open import NatIso

-- converting from homotopies of nat isos of 2-groups to equalities

module 2GrpMap-conv where

open CohGrp {{...}}

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}  where

  abstract
  
    ∘2G-conv-gen : {f₁ f₂ f₃ : CohGrpHom {{η₁}} {{η₂}}}
      (iso₁ : WkMagNatIso-forg f₁ f₃)
      (iso₂ : WkMagNatIso-forg f₁ f₂)
      (iso₃ : WkMagNatIso-forg f₂ f₃) →
      ∼WkMagNatIso iso₁ (iso₃ natiso-∘ iso₂)
      → natiso2G-to-== iso₁ == natiso2G-to-== iso₂ ∙ natiso2G-to-== iso₃
    ∘2G-conv-gen iso₁ iso₂ iso₃ e = natiso2G-to-==-∙ iso₂ iso₁ iso₃ e 
  
    ∘2G-conv : {f₁ f₂ f₃ : CohGrpHom {{η₁}} {{η₂}}}
      (iso₁ : WkMagNatIso-forg f₁ f₂) (iso₂ : WkMagNatIso-forg f₂ f₃) →
      natiso2G-to-== (iso₂ natiso-∘ iso₁) ◃∎ =ₛ natiso2G-to-== iso₁ ◃∙ natiso2G-to-== iso₂ ◃∎
    ∘2G-conv iso₁ iso₂ = =ₛ-in (∘2G-conv-gen (iso₂ natiso-∘ iso₁) iso₁ iso₂ (λ _ → idp))

    ∘2G-conv-tri : {f₁ f₂ f₃ f₄ : CohGrpHom {{η₁}} {{η₂}}}
      (iso₁ : WkMagNatIso-forg f₁ f₂) (iso₂ : WkMagNatIso-forg f₂ f₃)
      (iso₃ : WkMagNatIso-forg f₃ f₄) →
      natiso2G-to-== (iso₃ natiso-∘ iso₂ natiso-∘ iso₁) ◃∎
        =ₛ
      natiso2G-to-== iso₁ ◃∙ natiso2G-to-== iso₂ ◃∙ natiso2G-to-== iso₃ ◃∎
    ∘2G-conv-tri iso₁ iso₂ iso₃ =
      natiso2G-to-== (iso₃ natiso-∘ iso₂ natiso-∘ iso₁) ◃∎
        =ₛ⟨ ∘2G-conv (iso₂ natiso-∘ iso₁) iso₃ ⟩
      natiso2G-to-== (iso₂ natiso-∘ iso₁) ◃∙ natiso2G-to-== iso₃ ◃∎
        =ₛ⟨ 0 & 1 & ∘2G-conv iso₁ iso₂ ⟩
      natiso2G-to-== iso₁ ◃∙ natiso2G-to-== iso₂ ◃∙ natiso2G-to-== iso₃ ◃∎ ∎ₛ

  module _ {k} {G₃ : Type k} {{η₃ : CohGrp G₃}} where

    abstract
    
      whisk2G-conv-r : {f₁ : CohGrpHom {{η₁}} {{η₂}}} {f₂ f₂' : CohGrpHom {{η₂}} {{η₃}}}
        (iso : WkMagNatIso-forg f₂ f₂') →
        natiso2G-to-== (natiso-whisk-r iso) == ap (λ m → m ∘2G f₁) (natiso2G-to-== iso)
      whisk2G-conv-r iso = natiso2G-to-==-whisk-r iso (natiso-whisk-r iso) (λ _ → idp)

      whisk2G-conv-l : {f₂ : CohGrpHom {{η₂}} {{η₃}}} {f₁ f₁' : CohGrpHom {{η₁}} {{η₂}}}
        (iso : WkMagNatIso-forg f₁ f₁') →
        natiso2G-to-== (natiso-whisk-l {μ = grphom-forg f₂} iso) == ap (λ m → f₂ ∘2G m) (natiso2G-to-== iso)
      whisk2G-conv-l {f₂} iso = natiso2G-to-==-whisk-l iso (natiso-whisk-l {μ = grphom-forg f₂} iso) (λ _ → idp)

module _ {i j k} {G₁ : Type i} {G₂ : Type j} {G₃ : Type k}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}}
  {f₁ f₁' : CohGrpHom {{η₁}} {{η₂}}} {f₂ f₂' : CohGrpHom {{η₂}} {{η₃}}} where

  abstract
    tri-conv :
      (iso₂ : WkMagNatIso-forg f₁ f₁')
      (iso₃ : WkMagNatIso-forg f₂ f₂')
      (iso₁ : WkMagNatIso-forg (f₂ ∘2G f₁') (f₂' ∘2G f₁)) →
      ∼WkMagNatIso iso₁ ((natiso-whisk-r iso₃) natiso-∘ (!ʷ (natiso-whisk-l {μ = grphom-forg f₂} iso₂)))
      →
      natiso2G-to-== iso₁
        ==
      ! (ap (λ m → f₂ ∘2G m) (natiso2G-to-== iso₂)) ∙
      ap (λ m → m ∘2G f₁) (natiso2G-to-== iso₃)
    tri-conv iso₂ iso₃ iso₁ e = 
      natiso2G-to-== iso₁
        =⟨ ∘2G-conv-gen iso₁ (!ʷ (natiso-whisk-l {μ = grphom-forg f₂} iso₂)) (natiso-whisk-r iso₃) e ⟩
      natiso2G-to-== (!ʷ (natiso-whisk-l iso₂)) ∙ natiso2G-to-== (natiso-whisk-r iso₃)
        =⟨ ap2 _∙_ (natiso2G-! (natiso-whisk-l iso₂)) idp ⟩
      ! (natiso2G-to-== (natiso-whisk-l iso₂)) ∙ natiso2G-to-== (natiso-whisk-r iso₃)
        =⟨ ap2 _∙_ (ap ! (whisk2G-conv-l iso₂)) (whisk2G-conv-r iso₃) ⟩
      ! (ap (_∘2G_ f₂) (natiso2G-to-== iso₂)) ∙ ap (λ m → m ∘2G f₁) (natiso2G-to-== iso₃) =∎

module _ {i j k} {G₁ : Type i} {G₂ : Type j} {G₃ : Type k}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}}
  (f₁ : CohGrpHom {{η₁}} {{η₂}}) (f₂ : CohGrpHom {{η₂}} {{η₃}}) where

  tri-2G :
    natiso2G-to-== (assoc-wkmaghom (grphom-forg f₂) idf2Mw (grphom-forg f₁))
      ==
    ! (ap (λ m → f₂ ∘2G m) (natiso2G-to-== (unit-wkmaghom-l (grphom-forg f₁)))) ∙
    ap (λ m → m ∘2G f₁) (natiso2G-to-== (unit-wkmaghom-r (grphom-forg f₂)))
  tri-2G =
    tri-conv
      {f₁' = (cohgrphom (idf G₂) {{idf2G}}) ∘2G f₁}
      {f₂' = f₂ ∘2G (cohgrphom (idf G₂) {{idf2G}})}
      (unit-wkmaghom-l (grphom-forg f₁))
      (unit-wkmaghom-r (grphom-forg f₂))
      (assoc-wkmaghom (grphom-forg f₂) idf2Mw (grphom-forg f₁))
      λ _ → idp

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅} {G₁ : Type ℓ₁} {G₂ : Type ℓ₂} {G₃ : Type ℓ₃} {G₄ : Type ℓ₄} {G₅ : Type ℓ₅}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}} {{η₄ : CohGrp G₄}} {{η₅ : CohGrp G₅}}
  {f₁ : CohGrpHom {{η₁}} {{η₂}}} {f₂ : CohGrpHom {{η₁}} {{η₅}}} {f₃ f₆ : CohGrpHom {{η₁}} {{η₃}}}
  {f₄ : CohGrpHom {{η₃}} {{η₅}}} {f₅ f₇ : CohGrpHom {{η₂}} {{η₅}}} where

  abstract
    pent-conv :
      (iso₁ : WkMagNatIso-forg (f₄ ∘2G f₃) f₂) (iso₂ : WkMagNatIso-forg f₂ (f₅ ∘2G f₁))
      (iso₃ : WkMagNatIso-forg f₃ f₆) (iso₄ : WkMagNatIso-forg (f₄ ∘2G f₆) (f₇ ∘2G f₁))
      (iso₅ : WkMagNatIso-forg f₇ f₅) →
      ∼WkMagNatIso
        (iso₂ natiso-∘ iso₁)
        (natiso-whisk-r iso₅ natiso-∘ iso₄ natiso-∘ (natiso-whisk-l {μ = grphom-forg f₄} iso₃))
      →
      natiso2G-to-== iso₁ ∙ natiso2G-to-== iso₂
        ==
      ap (λ m → f₄ ∘2G m) (natiso2G-to-== iso₃) ∙
      natiso2G-to-== iso₄ ∙
      ap (λ m → m ∘2G f₁) (natiso2G-to-== iso₅)
    pent-conv iso₁ iso₂ iso₃ iso₄ iso₅ e = =ₛ-out $
      natiso2G-to-== iso₁ ◃∙ natiso2G-to-== iso₂ ◃∎
        =ₛ⟨ !ₛ (∘2G-conv iso₁ iso₂) ⟩
      natiso2G-to-== (iso₂ natiso-∘ iso₁) ◃∎
        =ₛ₁⟨ ap natiso2G-to-== (natiso∼-to-== e) ⟩
      natiso2G-to-== (natiso-whisk-r iso₅ natiso-∘ iso₄ natiso-∘ natiso-whisk-l iso₃) ◃∎
        =ₛ⟨ ∘2G-conv-tri (natiso-whisk-l iso₃) iso₄ (natiso-whisk-r iso₅) ⟩
      natiso2G-to-== (natiso-whisk-l iso₃) ◃∙
      natiso2G-to-== iso₄ ◃∙
      natiso2G-to-== (natiso-whisk-r iso₅) ◃∎  
        =ₛ₁⟨ 0 & 1 & whisk2G-conv-l iso₃ ⟩
      ap (λ m → f₄ ∘2G m) (natiso2G-to-== iso₃) ◃∙
      natiso2G-to-== iso₄ ◃∙
      natiso2G-to-== (natiso-whisk-r iso₅) ◃∎
        =ₛ₁⟨ 2 & 1 & whisk2G-conv-r iso₅ ⟩
      ap (λ m → f₄ ∘2G m) (natiso2G-to-== iso₃) ◃∙
      natiso2G-to-== iso₄ ◃∙
      ap (λ m → m ∘2G f₁) (natiso2G-to-== iso₅) ◃∎ ∎ₛ

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅} {G₁ : Type ℓ₁} {G₂ : Type ℓ₂} {G₃ : Type ℓ₃} {G₄ : Type ℓ₄} {G₅ : Type ℓ₅}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}} {{η₄ : CohGrp G₄}} {{η₅ : CohGrp G₅}}
  (f₁ : CohGrpHom {{η₁}} {{η₂}}) (f₂ : CohGrpHom {{η₂}} {{η₃}}) (f₃ : CohGrpHom {{η₃}} {{η₄}})
  (f₄ : CohGrpHom {{η₄}} {{η₅}})  where

  abstract
    pent-2G : 
      natiso2G-to-== {μ = f₄ ∘2G f₃ ∘2G f₂ ∘2G f₁} {ν = (f₄ ∘2G f₃) ∘2G (f₂ ∘2G f₁)}
        (assoc-wkmaghom (grphom-forg f₄) (grphom-forg f₃) (grphom-forg (f₂ ∘2G f₁))) ∙
      natiso2G-to-== (assoc-wkmaghom (grphom-forg (f₄ ∘2G f₃)) (grphom-forg f₂) (grphom-forg f₁))
        ==
      ap (λ m → f₄ ∘2G m)
        (natiso2G-to-== {μ = f₃ ∘2G f₂ ∘2G f₁} {ν = (f₃ ∘2G f₂) ∘2G f₁}
          (assoc-wkmaghom (grphom-forg f₃) (grphom-forg f₂) (grphom-forg f₁))) ∙
      natiso2G-to-== (assoc-wkmaghom (grphom-forg f₄) (grphom-forg (f₃ ∘2G f₂)) (grphom-forg f₁)) ∙
      ap (λ m → m ∘2G f₁)
        (natiso2G-to-== {μ = f₄ ∘2G f₃ ∘2G f₂} {ν = (f₄ ∘2G f₃) ∘2G f₂}
          (assoc-wkmaghom (grphom-forg f₄) (grphom-forg f₃) (grphom-forg f₂)))
    pent-2G = 
      pent-conv {{η₄ = η₄}}
        (assoc-wkmaghom (grphom-forg f₄) (grphom-forg f₃) (grphom-forg (f₂ ∘2G f₁)))
        (assoc-wkmaghom (grphom-forg (f₄ ∘2G f₃)) (grphom-forg f₂) (grphom-forg f₁))
        (assoc-wkmaghom (grphom-forg f₃) (grphom-forg f₂) (grphom-forg f₁))
        (assoc-wkmaghom (grphom-forg f₄) (grphom-forg (f₃ ∘2G f₂)) (grphom-forg f₁))
        (assoc-wkmaghom (grphom-forg f₄) (grphom-forg f₃) (grphom-forg f₂))
        λ _ → idp
