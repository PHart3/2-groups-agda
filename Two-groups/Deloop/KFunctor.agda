{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import 2Magma
open import 2Grp
open import Hmtpy2Grp

-- action of K₂ on maps

module KFunctor where

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} where

  open import Delooping

  instance
  
    K₂G₁-instance : has-level 2 (K₂ G₁ η₁)
    K₂G₁-instance = K₂-is-2type G₁

    K₂G₂-instance : has-level 2 (K₂ G₂ η₂)
    K₂G₂-instance = K₂-is-2type G₂

  open CohGrp {{...}}
  open CohGrpHom
  open WkMagHomStr

  K₂-map : {f : G₁ → G₂} (σ : WkMagHomStr f) → K₂ G₁ η₁ → K₂ G₂ η₂
  K₂-map {f} σ =
    K₂-rec G₁
      (base G₂)
      (loop' K₂-map-aux)
      (loop-comp' K₂-map-aux)
      (loop-assoc' K₂-map-aux)
    module _ where
      K₂-map-aux : Loop2Map {{mag η₁}} (base G₂)
      K₂-map-aux =
        wkmag-to-loop (base G₂)
        (loop-to-wkmag (base G₂)
          (loop2map-∙ (loop G₂) (loop-comp G₂) (loop-assoc G₂))
        ∘2M
        cohmaghom f {{σ}})

  module _ {f : G₁ → G₂} (σ : WkMagHomStr f) where

    K₂-map-β :
      WkMagNatIso
        (grphom-forg (Loop2Grp-map (K₂-map σ , idp)) ∘2Mw K₂-loophom G₁ {{η₁}})
        (loop-2map-forg (base G₂) (K₂-map-aux σ))
    WkMagNatIso.θ K₂-map-β = 
      loop-βr G₁
        (base G₂)
        (loop' (K₂-map-aux σ))
        (loop-comp' (K₂-map-aux σ))
        (loop-assoc' (K₂-map-aux σ))
    WkMagNatIso.θ-comp K₂-map-β = 
      loop-comp-βr G₁
        (base G₂)
        (loop' (K₂-map-aux σ))
        (loop-comp' (K₂-map-aux σ))
        (loop-assoc' (K₂-map-aux σ))

    K₂-map-β-pts : (x : G₁) → ap (K₂-map σ) (loop G₁ x) == loop G₂ (f x)
    K₂-map-β-pts x = WkMagNatIso.θ (K₂-map-β) x
