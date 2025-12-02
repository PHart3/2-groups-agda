{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import 2Semigroup
open import 2SGrpMap
open import 2Grp
open import 2GrpMap
open import NatIso

-- preservation of groupoid structure by natiso2G-to-==

module 2GrpMap-conv where

open CohGrp {{...}}

module 2G-comp-conv {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} where

  abstract
  
    ∘2G-conv-gen : {f₁ f₂ f₃ : CohGrpHom {{η₁}} {{η₂}}}
      (iso₁ : CohGrpNatIso f₁ f₃)
      (iso₂ : CohGrpNatIso f₁ f₂)
      (iso₃ : CohGrpNatIso f₂ f₃) →
      ∼WkSGrpNatIso iso₁ (iso₃ natiso-∘ iso₂)
      → natiso2G-to-== {μ = f₁} {ν = f₃} iso₁ == natiso2G-to-== {μ = f₁} {ν = f₂}iso₂ ∙ natiso2G-to-== iso₃
    ∘2G-conv-gen iso₁ iso₂ iso₃ e = natiso2G-to-==-∙ iso₂ iso₁ iso₃ e 
  
    ∘2G-conv : {f₁ f₂ f₃ : CohGrpHom {{η₁}} {{η₂}}}
      (iso₁ : CohGrpNatIso f₁ f₂) (iso₂ : CohGrpNatIso f₂ f₃) →
      natiso2G-to-== {μ = f₁} {ν = f₃} (iso₂ natiso-∘ iso₁) ◃∎
        =ₛ
      natiso2G-to-== {μ = f₁} {ν = f₂} iso₁ ◃∙ natiso2G-to-== iso₂ ◃∎
    ∘2G-conv {f₁} {f₂} {f₃} iso₁ iso₂ = =ₛ-in $
      ∘2G-conv-gen {f₁ = f₁} {f₂ = f₂} {f₃ = f₃} (iso₂ natiso-∘ iso₁) iso₁ iso₂ (λ _ → idp)

    ∘2G-conv-tri : {f₁ f₂ f₃ f₄ : CohGrpHom {{η₁}} {{η₂}}}
      (iso₁ : CohGrpNatIso f₁ f₂) (iso₂ : CohGrpNatIso f₂ f₃)
      (iso₃ : CohGrpNatIso f₃ f₄) →
      natiso2G-to-== {μ = f₁} {ν = f₄} (iso₃ natiso-∘ iso₂ natiso-∘ iso₁) ◃∎
        =ₛ
      natiso2G-to-== {μ = f₁} {ν = f₂} iso₁ ◃∙ natiso2G-to-== {μ = f₂} {ν = f₃} iso₂ ◃∙ natiso2G-to-== iso₃ ◃∎
    ∘2G-conv-tri {f₁} {f₃ = f₃} iso₁ iso₂ iso₃ =
      natiso2G-to-== (iso₃ natiso-∘ iso₂ natiso-∘ iso₁) ◃∎
        =ₛ⟨ ∘2G-conv {f₁ = f₁} {f₂ = f₃} (iso₂ natiso-∘ iso₁) iso₃ ⟩
      natiso2G-to-== (iso₂ natiso-∘ iso₁) ◃∙ natiso2G-to-== iso₃ ◃∎
        =ₛ⟨ 0 & 1 & ∘2G-conv iso₁ iso₂ ⟩
      natiso2G-to-== iso₁ ◃∙ natiso2G-to-== iso₂ ◃∙ natiso2G-to-== iso₃ ◃∎ ∎ₛ

    ∘2G-conv-quart : {f₁ f₂ f₃ f₄ f₅ : CohGrpHom {{η₁}} {{η₂}}}
      (iso₁ : CohGrpNatIso f₁ f₂) (iso₂ : CohGrpNatIso f₂ f₃)
      (iso₃ : CohGrpNatIso f₃ f₄) (iso₄ : CohGrpNatIso f₄ f₅) →
      natiso2G-to-== {μ = f₁} {ν = f₂} iso₁ ◃∙
      natiso2G-to-== {μ = f₂} {ν = f₃} iso₂ ◃∙
      natiso2G-to-== {μ = f₃} {ν = f₄} iso₃ ◃∙
      natiso2G-to-== {μ = f₄} {ν = f₅} iso₄ ◃∎ 
        =ₛ
      natiso2G-to-== (iso₄ natiso-∘ iso₃ natiso-∘ iso₂ natiso-∘ iso₁) ◃∎
    ∘2G-conv-quart iso₁ iso₂ iso₃ iso₄ = 
      natiso2G-to-== iso₁ ◃∙ natiso2G-to-== iso₂ ◃∙ natiso2G-to-== iso₃ ◃∙ natiso2G-to-== iso₄ ◃∎
        =ₛ⟨ 0 & 3 & !ₛ (∘2G-conv-tri iso₁ iso₂ iso₃) ⟩
      natiso2G-to-== (iso₃ natiso-∘ iso₂ natiso-∘ iso₁) ◃∙ natiso2G-to-== iso₄ ◃∎
        =ₛ⟨ !ₛ (∘2G-conv (iso₃ natiso-∘ iso₂ natiso-∘ iso₁) iso₄) ⟩
      natiso2G-to-== (iso₄ natiso-∘ iso₃ natiso-∘ iso₂ natiso-∘ iso₁) ◃∎ ∎ₛ

    ∘2G-conv-quint : {f₁ f₂ f₃ f₄ f₅ f₆ : CohGrpHom {{η₁}} {{η₂}}}
      (iso₁ : CohGrpNatIso f₁ f₂) (iso₂ : CohGrpNatIso f₂ f₃)
      (iso₃ : CohGrpNatIso f₃ f₄) (iso₄ : CohGrpNatIso f₄ f₅)
      (iso₅ : CohGrpNatIso f₅ f₆) →
      natiso2G-to-== {μ = f₁} {ν = f₂} iso₁ ◃∙
      natiso2G-to-== {μ = f₂} {ν = f₃} iso₂ ◃∙
      natiso2G-to-== {μ = f₃} {ν = f₄} iso₃ ◃∙
      natiso2G-to-== {μ = f₄} {ν = f₅} iso₄ ◃∙
      natiso2G-to-== {μ = f₅} {ν = f₆} iso₅ ◃∎ 
        =ₛ
      natiso2G-to-== (iso₅ natiso-∘ iso₄ natiso-∘ iso₃ natiso-∘ iso₂ natiso-∘ iso₁) ◃∎
    ∘2G-conv-quint iso₁ iso₂ iso₃ iso₄ iso₅ = 
      natiso2G-to-== iso₁ ◃∙
      natiso2G-to-== iso₂ ◃∙
      natiso2G-to-== iso₃ ◃∙
      natiso2G-to-== iso₄ ◃∙
      natiso2G-to-== iso₅ ◃∎
        =ₛ⟨ 0 & 4 & ∘2G-conv-quart iso₁ iso₂ iso₃ iso₄ ⟩
      natiso2G-to-== (iso₄ natiso-∘ iso₃ natiso-∘ iso₂ natiso-∘ iso₁) ◃∙
      natiso2G-to-== iso₅ ◃∎
        =ₛ⟨ !ₛ (∘2G-conv (iso₄ natiso-∘ iso₃ natiso-∘ iso₂ natiso-∘ iso₁) iso₅) ⟩
      natiso2G-to-== (iso₅ natiso-∘ iso₄ natiso-∘ iso₃ natiso-∘ iso₂ natiso-∘ iso₁) ◃∎ ∎ₛ

    ∘2G-conv-oct : {f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ : CohGrpHom {{η₁}} {{η₂}}}
      (iso₁ : CohGrpNatIso f₁ f₂) (iso₂ : CohGrpNatIso f₂ f₃)
      (iso₃ : CohGrpNatIso f₃ f₄) (iso₄ : CohGrpNatIso f₄ f₅)
      (iso₅ : CohGrpNatIso f₅ f₆) (iso₆ : CohGrpNatIso f₆ f₇)
      (iso₇ : CohGrpNatIso f₇ f₈) (iso₈ : CohGrpNatIso f₈ f₉) →
      natiso2G-to-== {μ = f₁} {ν = f₂} iso₁ ◃∙
      natiso2G-to-== {μ = f₂} {ν = f₃} iso₂ ◃∙
      natiso2G-to-== {μ = f₃} {ν = f₄} iso₃ ◃∙
      natiso2G-to-== {μ = f₄} {ν = f₅} iso₄ ◃∙
      natiso2G-to-== {μ = f₅} {ν = f₆} iso₅ ◃∙
      natiso2G-to-== {μ = f₆} {ν = f₇} iso₆ ◃∙
      natiso2G-to-== {μ = f₇} {ν = f₈} iso₇ ◃∙
      natiso2G-to-== {μ = f₈} {ν = f₉} iso₈ ◃∎
        =ₛ
      natiso2G-to-==
        (iso₈ natiso-∘ iso₇ natiso-∘ iso₆ natiso-∘ iso₅ natiso-∘ iso₄ natiso-∘ iso₃ natiso-∘ iso₂ natiso-∘ iso₁) ◃∎
    ∘2G-conv-oct iso₁ iso₂ iso₃ iso₄ iso₅ iso₆ iso₇ iso₈ = 
      natiso2G-to-== iso₁ ◃∙
      natiso2G-to-== iso₂ ◃∙
      natiso2G-to-== iso₃ ◃∙
      natiso2G-to-== iso₄ ◃∙
      natiso2G-to-== iso₅ ◃∙
      natiso2G-to-== iso₆ ◃∙
      natiso2G-to-== iso₇ ◃∙
      natiso2G-to-== iso₈ ◃∎
        =ₛ⟨ 0 & 5 & ∘2G-conv-quint iso₁ iso₂ iso₃ iso₄ iso₅ ⟩
      natiso2G-to-== (iso₅ natiso-∘ iso₄ natiso-∘ iso₃ natiso-∘ iso₂ natiso-∘ iso₁) ◃∙
      natiso2G-to-== iso₆ ◃∙
      natiso2G-to-== iso₇ ◃∙
      natiso2G-to-== iso₈ ◃∎
        =ₛ⟨ ∘2G-conv-quart (iso₅ natiso-∘ iso₄ natiso-∘ iso₃ natiso-∘ iso₂ natiso-∘ iso₁) iso₆ iso₇ iso₈ ⟩
      natiso2G-to-==
        (iso₈ natiso-∘ iso₇ natiso-∘ iso₆ natiso-∘ iso₅ natiso-∘ iso₄ natiso-∘ iso₃ natiso-∘ iso₂ natiso-∘ iso₁) ◃∎ ∎ₛ

  module Whisk-conv {k} {G₃ : Type k} {{η₃ : CohGrp G₃}} where

    abstract
    
      whisk2G-conv-r : {f₁ : CohGrpHom {{η₁}} {{η₂}}} {f₂ f₂' : CohGrpHom {{η₂}} {{η₃}}}
        (iso : CohGrpNatIso f₂ f₂') →
        natiso2G-to-== (natiso-whisk-r iso) == ap (λ m → m ∘2G f₁) (natiso2G-to-== {μ = f₂} {ν = f₂'} iso)
      whisk2G-conv-r {f₁} {f₂} {f₂'} iso =
        natiso2G-to-==-whisk-r {f₁ = f₁} {f₂ = f₂} {f₂' = f₂'} iso
          (natiso-whisk-r {μ = grphom-forg f₁} {ν₁ = grphom-forg f₂} {ν₂ = grphom-forg f₂'} iso) (λ _ → idp)

      !-whisk2G-conv-r : {f₁ : CohGrpHom {{η₁}} {{η₂}}} {f₂ f₂' : CohGrpHom {{η₂}} {{η₃}}}
        (iso : CohGrpNatIso f₂ f₂') →
        natiso2G-to-== (!ʷ (natiso-whisk-r iso)) == ! (ap (λ m → m ∘2G f₁) (natiso2G-to-== {μ = f₂} {ν = f₂'} iso))
      !-whisk2G-conv-r iso = natiso2G-! (natiso-whisk-r iso) ∙ ap ! (whisk2G-conv-r iso) 

      whisk2G-conv-l : {f₂ : CohGrpHom {{η₂}} {{η₃}}} {f₁ f₁' : CohGrpHom {{η₁}} {{η₂}}}
        (iso : CohGrpNatIso f₁ f₁') →
        natiso2G-to-== (natiso-whisk-l {μ = grphom-forg f₂} iso) == ap (λ m → f₂ ∘2G m) (natiso2G-to-== {μ = f₁} {ν = f₁'} iso)
      whisk2G-conv-l {f₂} iso =
        natiso2G-to-==-whisk-l {f₂ = f₂} iso (natiso-whisk-l {μ = grphom-forg f₂} iso) (λ _ → idp)

      !-whisk2G-conv-l : {f₂ : CohGrpHom {{η₂}} {{η₃}}} {f₁ f₁' : CohGrpHom {{η₁}} {{η₂}}}
        (iso : CohGrpNatIso f₁ f₁') →
        natiso2G-to-== (!ʷ (natiso-whisk-l {μ = grphom-forg f₂} iso)) == ! (ap (λ m → f₂ ∘2G m) (natiso2G-to-== {μ = f₁} {ν = f₁'} iso))
      !-whisk2G-conv-l {f₂} iso = natiso2G-! (natiso-whisk-l {μ = grphom-forg f₂} iso) ∙ ap ! (whisk2G-conv-l {f₂} iso)

  open Whisk-conv public

open 2G-comp-conv public

-- triangle identity

module _ {i j k} {G₁ : Type i} {G₂ : Type j} {G₃ : Type k}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}}
  {f₁ f₁' : CohGrpHom {{η₁}} {{η₂}}} {f₂ f₂' : CohGrpHom {{η₂}} {{η₃}}} where

  abstract
    tri-conv :
      (iso₂ : CohGrpNatIso f₁ f₁')
      (iso₃ : CohGrpNatIso f₂ f₂')
      (iso₁ : CohGrpNatIso (f₂ ∘2G f₁') (f₂' ∘2G f₁)) →
      ∼WkSGrpNatIso iso₁ ((natiso-whisk-r iso₃) natiso-∘ (!ʷ (natiso-whisk-l {μ = grphom-forg f₂} iso₂)))
      →
      natiso2G-to-== iso₁
        ==
      ! (ap (λ m → f₂ ∘2G m) (natiso2G-to-== {μ = f₁} {ν = f₁'} iso₂)) ∙
      ap (λ m → m ∘2G f₁) (natiso2G-to-== {μ = f₂} {ν = f₂'} iso₃)
    tri-conv iso₂ iso₃ iso₁ e = 
      natiso2G-to-== iso₁
        =⟨ ∘2G-conv-gen iso₁ (!ʷ (natiso-whisk-l {μ = grphom-forg f₂} iso₂)) (natiso-whisk-r iso₃) e ⟩
      natiso2G-to-== (!ʷ (natiso-whisk-l {μ = grphom-forg f₂} iso₂)) ∙
      natiso2G-to-== (natiso-whisk-r {μ = grphom-forg f₁} iso₃)
        =⟨ ap2 _∙_ (natiso2G-! (natiso-whisk-l {μ = grphom-forg f₂} iso₂)) idp ⟩
      ! (natiso2G-to-== (natiso-whisk-l {μ = grphom-forg f₂} iso₂)) ∙
      natiso2G-to-== (natiso-whisk-r {μ = grphom-forg f₁} iso₃)
        =⟨ ap2 _∙_ (ap ! (whisk2G-conv-l {f₂ = f₂} iso₂)) (whisk2G-conv-r iso₃) ⟩
      ! (ap (_∘2G_ f₂) (natiso2G-to-== iso₂)) ∙ ap (λ m → m ∘2G f₁) (natiso2G-to-== iso₃) =∎

module _ {i j k} {G₁ : Type i} {G₂ : Type j} {G₃ : Type k}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}}
  (f₁ : CohGrpHom {{η₁}} {{η₂}}) (f₂ : CohGrpHom {{η₂}} {{η₃}}) where

  tri-2G :
    natiso2G-to-== (assoc-wksgrphom (grphom-forg f₂) idf2Mw (grphom-forg f₁))
      ==
    ! (ap (λ m → f₂ ∘2G m)
        (natiso2G-to-== {μ = f₁} {ν = (cohgrphom (idf G₂) {{idf2G}}) ∘2G f₁} (unit-wksgrphom-l (grphom-forg f₁)))) ∙
    ap (λ m → m ∘2G f₁)
      (natiso2G-to-== {μ = f₂} {ν = f₂ ∘2G cohgrphom (idf G₂) {{idf2G}}} (unit-wksgrphom-r (grphom-forg f₂)))
  tri-2G =
    tri-conv
      {f₁' = (cohgrphom (idf G₂) {{idf2G}}) ∘2G f₁}
      {f₂' = f₂ ∘2G (cohgrphom (idf G₂) {{idf2G}})}
      (unit-wksgrphom-l (grphom-forg f₁))
      (unit-wksgrphom-r (grphom-forg f₂))
      (assoc-wksgrphom (grphom-forg f₂) idf2Mw (grphom-forg f₁))
      λ _ → idp

-- pentagon identity

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅} {G₁ : Type ℓ₁} {G₂ : Type ℓ₂} {G₃ : Type ℓ₃} {G₄ : Type ℓ₄} {G₅ : Type ℓ₅}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}} {{η₄ : CohGrp G₄}} {{η₅ : CohGrp G₅}}
  {f₁ : CohGrpHom {{η₁}} {{η₂}}} {f₂ : CohGrpHom {{η₁}} {{η₅}}} {f₃ f₆ : CohGrpHom {{η₁}} {{η₃}}}
  {f₄ : CohGrpHom {{η₃}} {{η₅}}} {f₅ f₇ : CohGrpHom {{η₂}} {{η₅}}} where

  abstract
    pent-conv :
      (iso₁ : CohGrpNatIso (f₄ ∘2G f₃) f₂) (iso₂ : CohGrpNatIso f₂ (f₅ ∘2G f₁))
      (iso₃ : CohGrpNatIso f₃ f₆) (iso₄ : CohGrpNatIso (f₄ ∘2G f₆) (f₇ ∘2G f₁))
      (iso₅ : CohGrpNatIso f₇ f₅) →
      ∼WkSGrpNatIso
        (iso₂ natiso-∘ iso₁)
        (natiso-whisk-r iso₅ natiso-∘ iso₄ natiso-∘ (natiso-whisk-l {μ = grphom-forg f₄} iso₃))
      →
      natiso2G-to-== {μ = f₄ ∘2G f₃} {ν = f₂} iso₁ ∙ natiso2G-to-== {μ = f₂} {ν = f₅ ∘2G f₁} iso₂
        ==
      ap (λ m → f₄ ∘2G m) (natiso2G-to-== {μ = f₃} {ν = f₆} iso₃) ∙
      natiso2G-to-== {μ = f₄ ∘2G f₆} {ν = f₇ ∘2G f₁} iso₄ ∙
      ap (λ m → m ∘2G f₁) (natiso2G-to-== {μ = f₇} {ν = f₅} iso₅)
    pent-conv iso₁ iso₂ iso₃ iso₄ iso₅ e = =ₛ-out $
      natiso2G-to-== iso₁ ◃∙ natiso2G-to-== iso₂ ◃∎
        =ₛ⟨ !ₛ (∘2G-conv iso₁ iso₂) ⟩
      natiso2G-to-== (iso₂ natiso-∘ iso₁) ◃∎
        =ₛ₁⟨ ap natiso2G-to-== (natiso∼-to-== e) ⟩
      natiso2G-to-== (natiso-whisk-r iso₅ natiso-∘ iso₄ natiso-∘ natiso-whisk-l {μ = grphom-forg f₄} iso₃) ◃∎
        =ₛ⟨ ∘2G-conv-tri (natiso-whisk-l {μ = grphom-forg f₄} iso₃) iso₄ (natiso-whisk-r {μ = grphom-forg f₁} iso₅) ⟩
      natiso2G-to-== (natiso-whisk-l {μ = grphom-forg f₄} iso₃) ◃∙
      natiso2G-to-== {μ = f₄ ∘2G f₆} {ν = f₇ ∘2G f₁} iso₄ ◃∙
      natiso2G-to-== (natiso-whisk-r {μ = grphom-forg f₁} iso₅) ◃∎  
        =ₛ₁⟨ 0 & 1 & whisk2G-conv-l {f₂ = f₄} iso₃ ⟩
      ap (λ m → f₄ ∘2G m) (natiso2G-to-== {μ = f₃} {ν = f₆} iso₃) ◃∙
      natiso2G-to-== {μ = f₄ ∘2G f₆} {ν = f₇ ∘2G f₁} iso₄ ◃∙
      natiso2G-to-== (natiso-whisk-r {μ = grphom-forg f₁} iso₅) ◃∎
        =ₛ₁⟨ 2 & 1 & whisk2G-conv-r {f₁ = f₁} iso₅ ⟩
      ap (λ m → f₄ ∘2G m) (natiso2G-to-== {μ = f₃} {ν = f₆} iso₃) ◃∙
      natiso2G-to-== {μ = f₄ ∘2G f₆} {ν = f₇ ∘2G f₁} iso₄ ◃∙
      ap (λ m → m ∘2G f₁) (natiso2G-to-== {μ = f₇} {ν = f₅} iso₅) ◃∎ ∎ₛ

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅} {G₁ : Type ℓ₁} {G₂ : Type ℓ₂} {G₃ : Type ℓ₃} {G₄ : Type ℓ₄} {G₅ : Type ℓ₅}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}} {{η₄ : CohGrp G₄}} {{η₅ : CohGrp G₅}}
  (f₁ : CohGrpHom {{η₁}} {{η₂}}) (f₂ : CohGrpHom {{η₂}} {{η₃}}) (f₃ : CohGrpHom {{η₃}} {{η₄}})
  (f₄ : CohGrpHom {{η₄}} {{η₅}}) where

  abstract
    pent-2G : 
      natiso2G-to-== {μ = f₄ ∘2G f₃ ∘2G f₂ ∘2G f₁} {ν = (f₄ ∘2G f₃) ∘2G (f₂ ∘2G f₁)}
        (assoc-wksgrphom (grphom-forg f₄) (grphom-forg f₃) (grphom-forg (f₂ ∘2G f₁))) ∙
      natiso2G-to-== (assoc-wksgrphom (grphom-forg (f₄ ∘2G f₃)) (grphom-forg f₂) (grphom-forg f₁))
        ==
      ap (λ m → f₄ ∘2G m)
        (natiso2G-to-== {μ = f₃ ∘2G f₂ ∘2G f₁} {ν = (f₃ ∘2G f₂) ∘2G f₁}
          (assoc-wksgrphom (grphom-forg f₃) (grphom-forg f₂) (grphom-forg f₁))) ∙
      natiso2G-to-== (assoc-wksgrphom (grphom-forg f₄) (grphom-forg (f₃ ∘2G f₂)) (grphom-forg f₁)) ∙
      ap (λ m → m ∘2G f₁)
        (natiso2G-to-== {μ = f₄ ∘2G f₃ ∘2G f₂} {ν = (f₄ ∘2G f₃) ∘2G f₂}
          (assoc-wksgrphom (grphom-forg f₄) (grphom-forg f₃) (grphom-forg f₂)))
    pent-2G = 
      pent-conv {{η₄ = η₄}}
        (assoc-wksgrphom (grphom-forg f₄) (grphom-forg f₃) (grphom-forg (f₂ ∘2G f₁)))
        (assoc-wksgrphom (grphom-forg (f₄ ∘2G f₃)) (grphom-forg f₂) (grphom-forg f₁))
        (assoc-wksgrphom (grphom-forg f₃) (grphom-forg f₂) (grphom-forg f₁))
        (assoc-wksgrphom (grphom-forg f₄) (grphom-forg (f₃ ∘2G f₂)) (grphom-forg f₁))
        (assoc-wksgrphom (grphom-forg f₄) (grphom-forg f₃) (grphom-forg f₂))
        λ _ → idp
