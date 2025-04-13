{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=5 #-}

open import lib.Basics
open import lib.types.LoopSpace
open import 2Semigroup
open import 2Grp
open import Hmtpy2Grp
open import Delooping

-- action of K₂ on maps

module KFunctor where

open CohGrp {{...}}

module _ {i} {G : Type i} {{η : CohGrp G}} where

  instance
    K₂G-instance : has-level 2 (K₂ G η)
    K₂G-instance = K₂-is-2type G

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} where

  open CohGrpHom
  open WkSGrpHomStr

  K₂-map : {f : G₁ → G₂} (σ : WkSGrpHomStr f) → K₂ G₁ η₁ → K₂ G₂ η₂
  K₂-map {f} σ =
    K₂-rec G₁
      (base G₂)
      (loop' K₂-map-aux)
      (loop-comp' K₂-map-aux)
      (loop-assoc' K₂-map-aux)
    module _ where
      K₂-map-aux : Loop2Map {{sgrp η₁}} (base G₂)
      K₂-map-aux =
        wksgrp-to-loop (base G₂)
        (loop-to-wksgrp (base G₂)
          (loop2map-∙ (loop G₂) (loop-comp G₂) (loop-assoc G₂))
        ∘2M
        cohsgrphom f {{σ}})


  K₂-map⊙ : {f : G₁ → G₂} (σ : WkSGrpHomStr f) → ⊙[ K₂ G₁ η₁ , base G₁ ] ⊙→ ⊙[ K₂ G₂ η₂ , base G₂ ]
  K₂-map⊙ σ = (K₂-map σ , idp)

  K₂-action-hom : CohGrpHom {{η₁}} {{η₂}} → ⊙[ K₂ G₁ η₁ , base G₁ ] ⊙→ ⊙[ K₂ G₂ η₂ , base G₂ ]
  K₂-action-hom (cohgrphom f {{σ}}) = K₂-map⊙ σ

  open WkSGrpNatIso

  module _ {f : G₁ → G₂} (σ : WkSGrpHomStr f) where

    K₂-map-β :
      WkSGrpNatIso
        (grphom-forg (Loop2Grp-map (K₂-map σ , idp)) ∘2Mw K₂-loophom G₁ {{η₁}})
        (loop-2map-forg (base G₂) (K₂-map-aux σ))
    θ K₂-map-β = 
      loop-βr G₁
        (base G₂)
        (loop' (K₂-map-aux σ))
        (loop-comp' (K₂-map-aux σ))
        (loop-assoc' (K₂-map-aux σ))
    θ-comp K₂-map-β = 
      loop-comp-βr G₁
        (base G₂)
        (loop' (K₂-map-aux σ))
        (loop-comp' (K₂-map-aux σ))
        (loop-assoc' (K₂-map-aux σ))

    K₂-map-β-pts : (x : G₁) → ap (K₂-map σ) (loop G₁ x) == loop G₂ (f x)
    K₂-map-β-pts = θ (K₂-map-β)

    K₂-map-β-comp : (x y : G₁)
      →
      K₂-map-β-pts (mu x y) ◃∎
        =ₛ
      ! (ap (ap (K₂-map σ)) (loop-comp G₁ x y)) ◃∙
      ! (∙-ap (K₂-map σ) (loop G₁ x) (loop G₁ y)) ◃∙
      ap2 mu (K₂-map-β-pts x) (K₂-map-β-pts y) ◃∙
      loop-comp G₂ (f x) (f y) ◃∙
      ap (loop G₂) (map-comp σ x y) ◃∎
    K₂-map-β-comp x y =
      K₂-map-β-pts (mu x y) ◃∎
        =ₛ⟨ θ-comp-rot (K₂-map-β) x y ⟩
      ! (∙-ap (K₂-map σ) (loop G₁ x) (loop G₁ y) ∙
      ap (ap (K₂-map σ)) (loop-comp G₁ x y)) ◃∙
      ap2 mu (K₂-map-β-pts x) (K₂-map-β-pts y) ◃∙
      (loop-comp G₂ (f x) (f y) ∙
      ap (loop G₂) (map-comp σ x y)) ◃∎
        =ₛ⟨ 2 & 1 & =ₛ-in idp ⟩
      ! (∙-ap (K₂-map σ) (loop G₁ x) (loop G₁ y) ∙
      ap (ap (K₂-map σ)) (loop-comp G₁ x y)) ◃∙
      ap2 mu (K₂-map-β-pts x) (K₂-map-β-pts y) ◃∙
      loop-comp G₂ (f x) (f y) ◃∙
      ap (loop G₂) (map-comp σ x y) ◃∎
        =ₛ⟨ 0 & 1 & 
          !-∙◃ (∙-ap (K₂-map σ) (loop G₁ x) (loop G₁ y)) (ap (ap (K₂-map σ)) (loop-comp G₁ x y)) ⟩
      ! (ap (ap (K₂-map σ)) (loop-comp G₁ x y)) ◃∙
      ! (∙-ap (K₂-map σ) (loop G₁ x) (loop G₁ y)) ◃∙
      ap2 mu (K₂-map-β-pts x) (K₂-map-β-pts y) ◃∙
      loop-comp G₂ (f x) (f y) ◃∙
      ap (loop G₂) (map-comp σ x y) ◃∎ ∎ₛ
