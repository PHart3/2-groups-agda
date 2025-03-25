{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=5 #-}

open import lib.Basics
open import lib.types.LoopSpace
open import 2Magma
open import 2Grp
open import Hmtpy2Grp

module LoopK where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open import Delooping G

  module _ {j} {X : Type j} {{trX : has-level 2 X}} (x₀ : X) {φ : G → x₀ == x₀} where

    K₂-rec-hom : WkMagHomStr {{mag η}} {{mag (Loop2Grp x₀)}} φ → ⊙[ K₂ η , base ] ⊙→ ⊙[ X , x₀ ]
    K₂-rec-hom ρ =
      let Λ = wkmag-to-loop x₀ (cohmaghom φ {{ρ}}) in
        K₂-rec x₀ (loop' Λ) (loop-comp' Λ) (loop-assoc' Λ) , idp

    module _ (ρ : WkMagHomStr {{mag η}} {{mag (Loop2Grp x₀)}} φ) where

      open WkMagNatIso

      K₂-rec-hom-β :
        WkMagNatIso
          (grphom-forg (Loop2Grp-map (K₂-rec-hom ρ)) ∘2Mw K₂-loophom {{η}})
          (maghom-forg (cohmaghom φ {{ρ}}))
      θ K₂-rec-hom-β = 
        let Λ = wkmag-to-loop x₀ (cohmaghom φ {{ρ}}) in
          loop-βr x₀
            (loop' Λ)
            (loop-comp' Λ)
            (loop-assoc' Λ)
      θ-comp K₂-rec-hom-β = 
        let Λ = wkmag-to-loop x₀ (cohmaghom φ {{ρ}}) in
          loop-comp-βr x₀
            (loop' Λ)
            (loop-comp' Λ)
            (loop-assoc' Λ)

      private
        ρ₀ = fst (K₂-rec-hom ρ)

      K₂-rec-hom-β-pts : (x : G) → ap ρ₀ (loop x) == φ x
      K₂-rec-hom-β-pts = θ K₂-rec-hom-β

      open CohGrp {{...}}
      
      open WkMagHomStr

      K₂-rec-hom-β-comp : (x y : G)
        →
        K₂-rec-hom-β-pts (mu x y) ◃∎
          =ₛ
        ! (∙-ap ρ₀ (loop x) (loop y) ∙ ap (ap ρ₀) (loop-comp x y)) ◃∙
        ap2 mu (K₂-rec-hom-β-pts x) (K₂-rec-hom-β-pts y) ◃∙
        map-comp ρ x y ◃∎
      K₂-rec-hom-β-comp = θ-comp-rot (K₂-rec-hom-β)

      ΩK₂-hom : Ω-fmap (K₂-rec-hom ρ) ∘ loop ∼ φ
      ΩK₂-hom z =
        let Λ = wkmag-to-loop x₀ (cohmaghom φ {{ρ}}) in
          loop-βr x₀ (loop' Λ) (loop-comp' Λ) (loop-assoc' Λ) z
