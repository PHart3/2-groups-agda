{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Sigma
open import 2Semigroup
open import 2SGrpMap
open import 2Grp
open import PostMultMap
open import Hmtpy2Grp

module Hmtpy2Grp2 where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open CohGrp η

  fst=-sect : WkSGrpNatIso (fst=-2map ∘2Mw sgrphom-forg (1tr-2SGrpMap G)) (idf2Mw {{sgrp (Loop2Grp G)}})
  WkSGrpNatIso.θ fst=-sect p = fst=-β p prop-has-all-paths-↓
  WkSGrpNatIso.θ-comp fst=-sect p₁ p₂ = lemma p₁ p₂
    where
      lemma : {A₁ A₂ A₃ : Type i} (q₁ : A₁ == A₂) (q₂ : A₂ == A₃)
        {d₁ : has-level 1 A₁} {d₂ : has-level 1 A₂} {d₃ : has-level 1 A₃}
        {t₁ : d₁ == d₂ [ has-level 1 ↓ q₁ ]} {t₂ : d₂ == d₃ [ has-level 1 ↓ q₂ ]}
        {t₃ : d₁ == d₃ [ has-level 1 ↓ q₁ ∙ q₂ ]} {t₄ : t₁ ∙ᵈ t₂ == t₃} →
        idp
          ==
        ! (ap2 _∙_ (fst=-β q₁ t₁) (fst=-β q₂ t₂)) ∙
        (∙-ap fst (pair= q₁ t₁) (pair= q₂ t₂) ∙
        ap (ap fst) (Σ-∙ {p = q₁} {p' = q₂} t₁ t₂ ∙ ap (pair= (q₁ ∙ q₂)) t₄)) ∙
        fst=-β (q₁ ∙ q₂) t₃
      lemma {A₁} idp idp {t₁ = t₁} {t₂} {t₄ = idp} = aux t₁ t₂
        where
          aux : {x₁ x₂ x₃ : has-level 1 A₁} (v₁ : x₁ == x₂) (v₂ : x₂ == x₃) → 
            idp
              ==
            ! (ap2 _∙_ (fst=-β {B = has-level 1} idp v₁) (fst=-β idp v₂)) ∙
            (∙-ap fst (ap (A₁ ,_) v₁) (ap (A₁ ,_) v₂) ∙
            ap (ap fst) (Σ-∙-aux v₁ v₂ ∙ idp)) ∙
            fst=-β {B = has-level 1} idp (v₁ ∙ v₂)
          aux idp idp = idp

  module Facts where

    abstract

      fst=-tri0 :
        WkSGrpNatIso
          (fst=-2map ∘2Mw loop-2map-forg (G , 1trunc) 2Grp-1Ty-lmap)
          ((fst=-2map ∘2Mw sgrphom-forg (1tr-2SGrpMap G)) ∘2Mw sgrphom-forg (ua-2SGrpMap G) ∘2Mw sgrphom-forg mu-≃-map)
      fst=-tri0 =
        fst=-2map ∘2Mw loop-2map-forg (G , 1trunc) 2Grp-1Ty-lmap
          =⟦ natiso-id (fst=-2map ∘2Mw loop-2map-forg (G , 1trunc) 2Grp-1Ty-lmap) ⟧
        fst=-2map ∘2Mw sgrphom-forg (1tr-2SGrpMap G) ∘2Mw sgrphom-forg (ua-2SGrpMap G) ∘2Mw sgrphom-forg mu-≃-map
          =⟦ assoc-wksgrphom fst=-2map (sgrphom-forg (1tr-2SGrpMap G)) (sgrphom-forg (ua-2SGrpMap G) ∘2Mw sgrphom-forg mu-≃-map) ⟧
        (fst=-2map ∘2Mw sgrphom-forg (1tr-2SGrpMap G)) ∘2Mw sgrphom-forg (ua-2SGrpMap G) ∘2Mw sgrphom-forg mu-≃-map ∎ₙ

      fst=-tri1 :
        WkSGrpNatIso
          ((fst=-2map ∘2Mw sgrphom-forg (1tr-2SGrpMap G)) ∘2Mw sgrphom-forg (ua-2SGrpMap G) ∘2Mw sgrphom-forg mu-≃-map)
          (sgrphom-forg (ua-2SGrpMap G) ∘2Mw sgrphom-forg mu-≃-map)
      fst=-tri1 =
        (fst=-2map ∘2Mw sgrphom-forg (1tr-2SGrpMap G)) ∘2Mw sgrphom-forg (ua-2SGrpMap G) ∘2Mw sgrphom-forg mu-≃-map
          =⟦ natiso-whisk-r fst=-sect ⟧
        idf2Mw ∘2Mw sgrphom-forg (ua-2SGrpMap G) ∘2Mw sgrphom-forg mu-≃-map
          =⟦ unit-wksgrphom (sgrphom-forg (ua-2SGrpMap G) ∘2Mw sgrphom-forg mu-≃-map) ⟧
        sgrphom-forg (ua-2SGrpMap G) ∘2Mw sgrphom-forg mu-≃-map ∎ₙ

  open Facts

  abstract
    fst=-tri :
      WkSGrpNatIso
        (fst=-2map ∘2Mw loop-2map-forg (G , 1trunc) 2Grp-1Ty-lmap)
        (sgrphom-forg (ua-2SGrpMap G) ∘2Mw sgrphom-forg mu-≃-map)
    fst=-tri = fst=-tri1 natiso-∘ fst=-tri0
