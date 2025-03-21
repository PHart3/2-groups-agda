{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

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

module 2GrpMap-conv where

open CohGrp {{...}}

module _ {i j k} {G₁ : Type i} {G₂ : Type j} {G₃ : Type k}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}}
  {f₁ f₁' : CohGrpHom {{η₁}} {{η₂}}} {f₂ f₂' : CohGrpHom {{η₂}} {{η₃}}} where

  tri-conv :
    (iso₂ : WkMagNatIso (grphom-forg f₁) (grphom-forg f₁'))
    (iso₃ : WkMagNatIso (grphom-forg f₂) (grphom-forg f₂'))
    (iso₁ : WkMagNatIso (grphom-forg (f₂ ∘2G f₁')) (grphom-forg (f₂' ∘2G f₁))) →
    ∼WkMagNatIso iso₁ ((natiso-whisk-r iso₃) natiso-∘ (!ʷ (natiso-whisk-l {μ = grphom-forg f₂} iso₂)))
    →
    natiso2G-to-== iso₁
      ==
    ! (ap (λ m → f₂ ∘2G m) (natiso2G-to-== iso₂)) ∙
    ap (λ m → m ∘2G f₁) (natiso2G-to-== iso₃)
  tri-conv iso₂ iso₃ = natiso2G-ind-bi
      (
      λ f₁' f₂' iso₂ iso₃ →
        (iso₁ : WkMagNatIso (grphom-forg (f₂ ∘2G f₁')) (grphom-forg (f₂' ∘2G f₁))) →
        ∼WkMagNatIso iso₁ ((natiso-whisk-r iso₃) natiso-∘ (!ʷ (natiso-whisk-l iso₂)))
        →
        natiso2G-to-== iso₁
          ==
        ! (ap (λ m → f₂ ∘2G m) (natiso2G-to-== iso₂)) ∙
        ap (λ m → m ∘2G f₁) (natiso2G-to-== iso₃))
    aux iso₂ iso₃
    where abstract
      aux : (iso : WkMagNatIso (grphom-forg (f₂ ∘2G f₁)) (grphom-forg (f₂ ∘2G f₁))) →
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
          lemma : ∼WkMagNatIso iso (natiso-id (grphom-forg (f₂ ∘2G f₁)))
          lemma = coe (ap (∼WkMagNatIso iso) {!!}) e
          
          aux2 : ∼WkMagNatIso iso (natiso-id (grphom-forg (f₂ ∘2G f₁))) → natiso2G-to-== iso == idp
          aux2 h = ap natiso2G-to-== (natiso∼-to-== h) ∙ natiso2G-to-==-β (f₂ ∘2G f₁)
