{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=2 --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import 2Magma
open import 2Grp
open import Delooping
open import KFunctor
open import K-hom-ind
open import K-hom2-ind
open import apK-aux2

-- action of K₂ on 2-cells

module apK where

open CohGrp {{...}}

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {f₁ f₂ : G₁ → G₂}
  {σ₁ : WkMagHomStr f₁} {σ₂ : WkMagHomStr f₂} where

  open WkMagNatIso

  apK₂ : WkMagNatIso (maghom-forg (cohmaghom f₁ {{σ₁}})) (maghom-forg (cohmaghom f₂ {{σ₂}})) → K₂-map⊙ σ₁ ⊙-comp K₂-map⊙ σ₂
  fst (apK₂ iso) = 
    K₂-∼-ind (fst (K₂-map⊙ σ₁)) (fst (K₂-map⊙ σ₂))
    idp
    (λ x → K₂-map-β-pts σ₁ x ∙ ap (loop G₂) (θ iso x) ∙ ! (K₂-map-β-pts σ₂ x))
    (apK₂-coher iso)
  snd (apK₂ iso) = idp


module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {f : G₁ → G₂} {σ : WkMagHomStr f} where

  abstract
    apK₂-idp-coher : (x : G₁) →
      hmtpy-nat-∙'
        (λ v →
           K₂-∼-ind (fst (K₂-map⊙ σ)) (fst (K₂-map⊙ σ)) idp
             (λ z → K₂-map-β-pts σ z ∙ ! (K₂-map-β-pts σ z))
           (apK₂-coher (natiso-id (maghom-forg (cohmaghom f {{σ}})))) v)
        (loop G₁ x)
        ==
      hmtpy-nat-∙' (λ v → idp) (loop G₁ x)
    apK₂-idp-coher x =
      hmtpy-nat-∙'
        (λ v →
           K₂-∼-ind (fst (K₂-map⊙ σ)) (fst (K₂-map⊙ σ)) idp
             (λ z → K₂-map-β-pts σ z ∙ ! (K₂-map-β-pts σ z))
           (apK₂-coher (natiso-id (maghom-forg (cohmaghom f {{σ}})))) v)
        (loop G₁ x)
        =⟨ K₂-∼-ind-β (fst (K₂-map⊙ σ)) (fst (K₂-map⊙ σ)) idp (λ z → K₂-map-β-pts σ z ∙ ! (K₂-map-β-pts σ z)) _ x ⟩
      K₂-map-β-pts σ x ∙ ! (K₂-map-β-pts σ x)
        =⟨ !-inv-r (K₂-map-β-pts σ x) ⟩
      idp
        =⟨ ! (hmtpy-nat-∙'-idp (loop G₁ x)) ⟩
      hmtpy-nat-∙' (λ v → idp) (loop G₁ x) =∎

  abstract
    apK₂-idp : apK₂ (natiso-id (maghom-forg (cohmaghom f {{σ}}))) ⊙→∼ ⊙∼-id (K₂-map⊙ σ)
    fst apK₂-idp = K₂-∼∼-ind idp apK₂-idp-coher
    snd apK₂-idp = =ₛ-in idp
