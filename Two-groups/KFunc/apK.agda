{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=2 #-}

open import lib.Basics
open import lib.types.Pointed
open import 2Semigroup
open import 2Grp
open import 2GrpMap
open import Delooping
open import KFunctor
open import K-hom-ind
open import K-hom2-ind
open import apK-aux2

-- action of K₂ on 2-cells

module apK where

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {f₁ f₂ : G₁ → G₂}
  {σ₁ : WkSGrpHomStr f₁} {σ₂ : WkSGrpHomStr f₂} where

  private
    m₁ = sgrphom-forg (cohsgrphom f₁ {{σ₁}})
    m₂ = sgrphom-forg (cohsgrphom f₂ {{σ₂}})

  open WkSGrpNatIso

  apK₂ : WkSGrpNatIso m₁ m₂ → K₂-map⊙ σ₁ ⊙-comp K₂-map⊙ σ₂
  fst (apK₂ iso) = 
    K₂-∼-ind (fst (K₂-map⊙ σ₁)) (fst (K₂-map⊙ σ₂))
    idp
    (λ x → K₂-map-β-pts σ₁ x ∙ ap (loop G₂) (θ iso x) ∙ ! (K₂-map-β-pts σ₂ x))
    (apK₂-coher iso)
  snd (apK₂ iso) = idp

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {f : G₁ → G₂} {σ : WkSGrpHomStr f} where

  abstract
    apK₂-idp-coher : (x : G₁) →
      hmtpy-nat-∙'
        (λ v →
           K₂-∼-ind (fst (K₂-map⊙ σ)) (fst (K₂-map⊙ σ)) idp
             (λ z → K₂-map-β-pts σ z ∙ ! (K₂-map-β-pts σ z))
           (apK₂-coher (natiso-id (sgrphom-forg (cohsgrphom f {{σ}})))) v)
        (loop G₁ x)
        ==
      hmtpy-nat-∙' (λ v → idp) (loop G₁ x)
    apK₂-idp-coher x =
      hmtpy-nat-∙'
        (λ v →
           K₂-∼-ind (fst (K₂-map⊙ σ)) (fst (K₂-map⊙ σ)) idp
             (λ z → K₂-map-β-pts σ z ∙ ! (K₂-map-β-pts σ z))
           (apK₂-coher (natiso-id (sgrphom-forg (cohsgrphom f {{σ}})))) v)
        (loop G₁ x)
        =⟨ K₂-∼-ind-β (fst (K₂-map⊙ σ)) (fst (K₂-map⊙ σ)) idp (λ z → K₂-map-β-pts σ z ∙ ! (K₂-map-β-pts σ z)) _ x ⟩
      K₂-map-β-pts σ x ∙ ! (K₂-map-β-pts σ x)
        =⟨ !-inv-r (K₂-map-β-pts σ x) ⟩
      idp
        =⟨ ! (hmtpy-nat-∙'-idp (loop G₁ x)) ⟩
      hmtpy-nat-∙' (λ v → idp) (loop G₁ x) =∎

  apK₂-idp : apK₂ (natiso-id (sgrphom-forg (cohsgrphom f {{σ}}))) ⊙→∼ ⊙∼-id (K₂-map⊙ σ)
  fst apK₂-idp = K₂-∼∼-ind idp apK₂-idp-coher
  snd apK₂-idp = idp

module aux-hide {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {φ₁ : CohGrpHom {{η₁}} {{η₂}}} where

  abstract
    apK₂-pres-aux : ap K₂-action-hom (natiso2G-to-== {μ = φ₁} {ν = φ₁} (natiso-id2G φ₁)) == ⊙-comp-to-== (apK₂ (natiso-id2G φ₁))
    apK₂-pres-aux = ap (ap K₂-action-hom) (natiso2G-to-==-β φ₁) ∙ ! (ap ⊙-comp-to-== (⊙→∼-to-== apK₂-idp) ∙ ⊙-comp-to-==-β (K₂-action-hom φ₁))

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {φ₁@(cohgrphom f₁ {{σ₁}}) : CohGrpHom {{η₁}} {{η₂}}} where

  open aux-hide {φ₁ = φ₁}

  abstract
    apK₂-pres : {φ₂@(cohgrphom f₂ {{σ₂}}) : CohGrpHom {{η₁}} {{η₂}}} (iso : CohGrpNatIso φ₁ φ₂)
      → ap K₂-action-hom (natiso2G-to-== {μ = φ₁} {ν = φ₂} iso) == ⊙-comp-to-== (apK₂ {f₁ = f₁} {f₂ = f₂} {σ₁ = σ₁} {σ₂ = σ₂} iso) 
    apK₂-pres =
      natiso2G-ind {μ = φ₁}
        (λ φ₂@(cohgrphom f₂ {{σ₂}}) iso →
          ap K₂-action-hom (natiso2G-to-== {μ = φ₁} {ν = φ₂} iso) == ⊙-comp-to-== (apK₂ {f₁ = f₁} {f₂ = f₂} {σ₁ = σ₁} {σ₂ = σ₂} iso))
        apK₂-pres-aux
