{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import 2Semigroup
open import 2SGrpMap
open import 2Grp
open import Delooping
open import K-hom-ind
open import KFunctor
open import KFunctor-comp
open import apK

module KFunctor-comp-assoc-aux0 where

module KFCA0 {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {G₁ : Type ℓ₁} {G₂ : Type ℓ₂} {G₃ : Type ℓ₃} {G₄ : Type ℓ₄}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}} {{η₄ : CohGrp G₄}}
  {f₁ : G₁ → G₂} (σ₁ : WkSGrpHomStr f₁) {f₂ : G₂ → G₃}
  (σ₂ : WkSGrpHomStr f₂) {f₃ : G₃ → G₄} (σ₃ : WkSGrpHomStr f₃) (x : G₁) where

  open import KFunctor-comp-assoc-defs σ₁ σ₂ σ₃

  abstract

    K₂-β-1 : hmtpy-nat-∙' (fst (K₂-map-∘ σ₁ σ₂)) (loop G₁ x) ◃∎ =ₛ δ₁ x
    K₂-β-1 = =ₛ-in (K₂-∼-ind-β (map₁-∘ σ₁ σ₂) (map₂-∘ σ₁ σ₂) idp ν₁ _ x)

    K₂-β-2 : hmtpy-nat-∙' (fst (K₂-map-∘ (m₂ ∘2Mσ m₁) σ₃)) (loop G₁ x) ◃∎ =ₛ δ₂ x
    K₂-β-2 = =ₛ-in (K₂-∼-ind-β (map₁-∘ (m₂ ∘2Mσ m₁) σ₃) (map₂-∘ (m₂ ∘2Mσ m₁) σ₃) idp ν₂ _ x)

    K₂-β-3 : hmtpy-nat-∙' (fst (apK₂ (assoc-wksgrphom (sgrphom-forg m₃) (sgrphom-forg m₂) (sgrphom-forg m₁)))) (loop G₁ x) ◃∎ =ₛ δ₃ x
    K₂-β-3 = =ₛ-in (K₂-∼-ind-β (K₂-map (m₃ ∘2Mσ (m₂ ∘2M m₁))) (K₂-map ((m₃ ∘2M m₂) ∘2Mσ m₁)) (idp {a = base G₄}) ν₃ _ x)

    K₂-β-4 : hmtpy-nat-∙' (fst (K₂-map-∘ σ₁ (m₃ ∘2Mσ m₂))) (loop G₁ x) ◃∎ =ₛ δ₄ x
    K₂-β-4 = =ₛ-in (K₂-∼-ind-β (map₁-∘ σ₁ (m₃ ∘2Mσ m₂)) (map₂-∘ σ₁ (m₃ ∘2Mσ m₂)) idp ν₄ _ x)

    K₂-β-5 : hmtpy-nat-∙' (fst (K₂-map-∘ σ₂ σ₃)) (ap (K₂-map σ₁) (loop G₁ x)) ◃∎ =ₛ δ₅ x
    K₂-β-5 =
      hmtpy-nat-∙' (fst (K₂-map-∘ σ₂ σ₃)) (ap (K₂-map σ₁) (loop G₁ x)) ◃∎
        =ₛ⟨ apCommSq2◃-rev (λ (p : base G₂ == base G₂) → hmtpy-nat-∙' (fst (K₂-map-∘ σ₂ σ₃)) p) (K₂-map-β-pts σ₁ x) ⟩
      ap (ap (K₂-map (m₃ ∘2Mσ m₂))) (K₂-map-β-pts σ₁ x) ◃∙
      hmtpy-nat-∙' (fst (K₂-map-∘ σ₂ σ₃)) (loop G₂ (f₁ x)) ◃∙
      ! (ap (ap (K₂-map σ₃ ∘ K₂-map σ₂)) (K₂-map-β-pts σ₁ x)) ◃∎
        =ₑ⟨ 1 & 1 &
            (K₂-map-β-pts (m₃ ∘2Mσ m₂) (f₁ x) ◃∙
            ! (K₂-map-β-pts σ₃ (f₂ (f₁ x))) ◃∙
            ! (ap (ap (K₂-map σ₃)) (K₂-map-β-pts σ₂ (f₁ x))) ◃∙
            ∘-ap (K₂-map σ₃) (K₂-map σ₂) (loop G₂ (f₁ x)) ◃∎)
          % =ₛ-in (K₂-∼-ind-β (map₁-∘ σ₂ σ₃) (map₂-∘ σ₂ σ₃) idp ν₅ _ (f₁ x)) ⟩
      δ₅ x ∎ₛ
        
