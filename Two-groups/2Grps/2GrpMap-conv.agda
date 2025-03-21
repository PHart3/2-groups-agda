{-# OPTIONS --without-K --rewriting --overlapping-instances --lossy-unification #-}

open import lib.Basics
open import lib.FTID
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Paths
open import 2Magma
open import 2MagMap
open import 2Grp
open import 2GrpMap
open import NatIso

-- converting from homotopies of nat isos of 2-groups to equalities

module 2GrpMap-conv where

open CohGrp {{...}}

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}  where

  ∘2G-conv : {f₁ f₂ f₃ : CohGrpHom {{η₁}} {{η₂}}}
    (iso₁ : WkMagNatIso-forg f₁ f₃)
    (iso₂ : WkMagNatIso-forg f₁ f₂)
    (iso₃ : WkMagNatIso-forg f₂ f₃) →
    ∼WkMagNatIso iso₁ (iso₃ natiso-∘ iso₂)
    → natiso2G-to-== iso₁ == natiso2G-to-== iso₂ ∙ natiso2G-to-== iso₃
  ∘2G-conv iso₁ iso₂ iso₃ e = natiso2G-to-==-∙ iso₂ iso₁ iso₃ e 

  !2G-conv : {f : CohGrpHom {{η₁}} {{η₂}}} (iso₁ iso₂ : WkMagNatIso-forg f f) →
    ∼WkMagNatIso iso₁ (!ʷ iso₂) → natiso2G-to-== iso₁ == ! (natiso2G-to-== iso₂)
  !2G-conv = natiso2G-to-==-!

  module _ {k} {G₃ : Type k} {{η₃ : CohGrp G₃}} where

    whisk2G-conv-r : {f₁ : CohGrpHom {{η₁}} {{η₂}}} {f₂ f₂' : CohGrpHom {{η₂}} {{η₃}}}
      (iso₁ : WkMagNatIso-forg (f₂ ∘2G f₁) (f₂' ∘2G f₁)) (iso₂ : WkMagNatIso-forg f₂ f₂') →
      ∼WkMagNatIso iso₁ (natiso-whisk-r iso₂)
      → natiso2G-to-== iso₁ == ap (λ m → m ∘2G f₁) (natiso2G-to-== iso₂)
    whisk2G-conv-r iso₁ iso₂ e = {!!}

    whisk2G-conv-l : {f₂ : CohGrpHom {{η₂}} {{η₃}}} {f₁ f₁' : CohGrpHom {{η₁}} {{η₂}}}
      (iso₁ : WkMagNatIso-forg (f₂ ∘2G f₁) (f₂ ∘2G f₁')) (iso₂ : WkMagNatIso-forg f₁ f₁') →
      ∼WkMagNatIso iso₁ (natiso-whisk-l {μ = grphom-forg f₂} iso₂)
      → natiso2G-to-== iso₁ == ap (λ m → f₂ ∘2G m) (natiso2G-to-== iso₂)
    whisk2G-conv-l iso₁ iso₂ e = {!!}

{-
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
    tri-conv iso₂ iso₃ iso₁ = {- natiso2G-ind-bi {f₁ = f₁} {f₂ = f₂}
        (
        λ f₁' f₂' iso₂ iso₃ →
          (iso₁ : WkMagNatIso-forg (f₂ ∘2G f₁') (f₂' ∘2G f₁)) →
          ∼WkMagNatIso iso₁ ((natiso-whisk-r iso₃) natiso-∘ (!ʷ (natiso-whisk-l {μ = grphom-forg f₂} iso₂)))
          →
          natiso2G-to-== iso₁
            ==
          ! (ap (λ m → f₂ ∘2G m) (natiso2G-to-== iso₂)) ∙
          ap (λ m → m ∘2G f₁) (natiso2G-to-== iso₃))
      aux {f₁' = f₁'} {f₂' = f₂'} iso₂ iso₃
      where abstract
        aux : (iso : WkMagNatIso-forg (f₂ ∘2G f₁) (f₂ ∘2G f₁)) →
          ∼WkMagNatIso iso
            ((natiso-whisk-r (natiso-id (grphom-forg f₂)))
              natiso-∘
            (!ʷ (natiso-whisk-l {μ = grphom-forg f₂} (natiso-id (grphom-forg f₁)))))
          →
          natiso2G-to-== iso
            ==
          ! (ap (λ m → f₂ ∘2G m) (natiso2G-to-== (natiso-id (grphom-forg f₁)))) ∙
          ap (λ m → m ∘2G f₁) (natiso2G-to-== (natiso-id (grphom-forg f₂)))
        aux iso e =
          natiso2G-to-== iso
            =⟨ aux2 lemma ⟩
          idp
            =⟨ ! (ap2 _∙_
                   (ap ! (ap (ap (λ m → f₂ ∘2G m)) (natiso2G-to-==-β f₁)))
                   (ap (ap (λ m → m ∘2G f₁)) (natiso2G-to-==-β f₂))) ⟩
          ! (ap (λ m → f₂ ∘2G m) (natiso2G-to-== (natiso-id (grphom-forg f₁)))) ∙
          ap (λ m → m ∘2G f₁) (natiso2G-to-== (natiso-id (grphom-forg f₂))) =∎
          where
            lemma-aux :
              (natiso-whisk-r (natiso-id (grphom-forg f₂)))
                natiso-∘
              (!ʷ (natiso-whisk-l {μ = grphom-forg f₂} (natiso-id (grphom-forg f₁))))
                ==
              natiso-id (grphom-forg (f₂ ∘2G f₁))
            lemma-aux = natiso∼-to-== λ _ → idp 
            
            lemma : ∼WkMagNatIso iso (natiso-id (grphom-forg (f₂ ∘2G f₁)))
            lemma = coe (ap (∼WkMagNatIso iso) lemma-aux) e

            aux2 : ∼WkMagNatIso iso (natiso-id (grphom-forg (f₂ ∘2G f₁)))
              → natiso2G-to-== {μ = f₂ ∘2G f₁} {ν = f₂ ∘2G f₁} iso == idp
            aux2 h = ap natiso2G-to-== (natiso∼-to-== h) ∙ natiso2G-to-==-β (f₂ ∘2G f₁) -}

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


-}
