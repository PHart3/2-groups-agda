{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import Biequiv
open import 2Grp
open import 2Magma
open import 2MagMap
open import NatIso
open import 2GrpMap
open import 2GrpMap-conv
open import 2GrpSIP
open import 2Grp-bc

module 2Grp-ae where

-- an equivalence of 2-groups is an adjoint equivalence

module _ {i} {G₁ : Type i} {η₁ : CohGrp G₁} where

  open CohGrpHom
  open Adjequiv

  abstract
    2g≃-to-adjeq : {(_ , η₂) : Σ (Type i) (λ G₂ → CohGrp G₂)} →
      (((map , _) , σ) : η₁ 2g≃ η₂) → Adjequiv (cohgrphom {{η₁}} {{η₂}} map {{σ}})
    2g≃-to-adjeq = 
      2grphom-ind
        (λ ((_ , η₂) : Σ (Type i) (λ G₂ → CohGrp G₂)) (((map , _) , σ) : η₁ 2g≃ η₂)
          → Adjequiv (cohgrphom {{η₁}} {{η₂}} map {{σ}}))
        (adj-str {{η₁}})
        where
          adj-str : {{η : CohGrp G₁}} → Adjequiv (cohgrphom {{η}} {{η}} (idf G₁) {{idf2G {{η}}}})
          map (inv adj-str) = idf G₁
          str (inv adj-str) = idf2G
          eta adj-str = natiso2G-to-== (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))
          eps adj-str = natiso2G-to-== (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))
          coher-map (adj-str {{η}}) = let idfη = cohgrphom (idf G₁) {{idf2G}} in
            =ₛ-out $
              natiso2G-to-== (unit-wkmaghom-r (grphom-forg idfη)) ◃∙
              ap (λ m → idfη ∘2G m)
                (natiso2G-to-== (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))) ◃∙
              natiso2G-to-== (assoc-wkmaghom (grphom-forg idfη) (grphom-forg (inv adj-str)) (grphom-forg idfη)) ◃∎
                =ₛ₁⟨ 1 & 1 & ! (whisk2G-conv-l (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))) ⟩
              natiso2G-to-== (unit-wkmaghom-r (grphom-forg idfη)) ◃∙
              natiso2G-to-== (natiso-whisk-l {{η₂ = mag η}} {ν₁ = grphom-forg idfη} (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))) ◃∙
              natiso2G-to-== (assoc-wkmaghom (grphom-forg idfη) (grphom-forg (inv adj-str)) (grphom-forg idfη)) ◃∎
                =ₛ⟨ !ₛ (
                      ∘2G-conv-tri
                        (unit-wkmaghom-r (grphom-forg idfη))
                        (natiso-whisk-l {{η₂ = mag η}} {ν₁ = grphom-forg idfη} (cohgrpnatiso (λ _ → idp) (λ _ _ → idp)))
                        (assoc-wkmaghom (grphom-forg idfη) (grphom-forg (inv adj-str)) (grphom-forg idfη))) ⟩
              natiso2G-to-==
                (assoc-wkmaghom (grphom-forg idfη) (wkmaghom (idf G₁) (λ x y → idp)) (grphom-forg idfη)
                  natiso-∘
                natiso-whisk-l {{η₂ = mag η}} {ν₁ = grphom-forg idfη} (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))
                  natiso-∘
                unit-wkmaghom-r (grphom-forg idfη)) ◃∎
                =ₛ₁⟨ ap natiso2G-to-== (natiso∼-to-== (λ _ → idp)) ⟩
              natiso2G-to-==
                (natiso-whisk-r (cohgrpnatiso (λ _ → idp) (λ _ _ → idp)) natiso-∘ unit-wkmaghom-l (grphom-forg idfη)) ◃∎
                =ₛ⟨ ∘2G-conv
                      (unit-wkmaghom-l (grphom-forg idfη))
                      (natiso-whisk-r {{η₂ = mag η}} {μ = grphom-forg idfη} (cohgrpnatiso (λ _ → idp) (λ _ _ → idp)))  ⟩
              natiso2G-to-== (unit-wkmaghom-l (grphom-forg idfη)) ◃∙
              natiso2G-to-== (natiso-whisk-r {{η₂ = mag η}} {μ = grphom-forg idfη} (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))) ◃∎
                =ₛ₁⟨ 1 & 1 & whisk2G-conv-r (cohgrpnatiso (λ _ → idp) (λ _ _ → idp)) ⟩
              natiso2G-to-== (unit-wkmaghom-l (grphom-forg idfη)) ◃∙
              ap (λ m → m ∘2G idfη)
                (natiso2G-to-== (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))) ◃∎ ∎ₛ            
          coher-inv (adj-str {{η}}) = let idfη = cohgrphom (idf G₁) {{idf2G}} in
            =ₛ-out $
              natiso2G-to-== (unit-wkmaghom-l (grphom-forg idfη)) ◃∙
              ap (λ m → m ∘2G idfη) (natiso2G-to-== (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))) ◃∎
                =ₛ₁⟨ 1 & 1 & ! (whisk2G-conv-r (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))) ⟩
              natiso2G-to-== (unit-wkmaghom-l (grphom-forg idfη)) ◃∙
              natiso2G-to-== (natiso-whisk-r {{η₂ = mag η}} {μ = grphom-forg idfη} (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))) ◃∎
                =ₛ⟨ !ₛ
                      (∘2G-conv (unit-wkmaghom-l (grphom-forg idfη)) (natiso-whisk-r {{η₂ = mag η}} {μ = grphom-forg idfη}
                        (cohgrpnatiso (λ _ → idp) (λ _ _ → idp)))) ⟩
              natiso2G-to-== (natiso-whisk-r (cohgrpnatiso (λ _ → idp) (λ _ _ → idp)) natiso-∘ unit-wkmaghom-l (grphom-forg idfη)) ◃∎
                =ₛ₁⟨ ap natiso2G-to-== (natiso∼-to-== (λ _ → idp)) ⟩
              natiso2G-to-== (
                assoc-wkmaghom (grphom-forg idfη) (grphom-forg idfη) (grphom-forg idfη)
                  natiso-∘
                natiso-whisk-l {{η₂ = mag η}} {ν₁ = grphom-forg idfη} (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))
                  natiso-∘
                unit-wkmaghom-r (grphom-forg idfη)) ◃∎
                =ₛ⟨ ∘2G-conv-tri
                      (unit-wkmaghom-r (grphom-forg idfη))
                      (natiso-whisk-l {{η₂ = mag η}} {ν₁ = grphom-forg idfη} (cohgrpnatiso (λ _ → idp) (λ _ _ → idp)))
                      (assoc-wkmaghom (grphom-forg idfη) (grphom-forg idfη) (grphom-forg idfη)) ⟩
              natiso2G-to-== (unit-wkmaghom-r (grphom-forg idfη)) ◃∙
              natiso2G-to-== (natiso-whisk-l {{η₂ = mag η}} {ν₁ = grphom-forg idfη} (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))) ◃∙
              natiso2G-to-== (assoc-wkmaghom (grphom-forg idfη) (grphom-forg idfη) (grphom-forg idfη)) ◃∎
                =ₛ₁⟨ 1 & 1 & whisk2G-conv-l (cohgrpnatiso (λ _ → idp) (λ _ _ → idp)) ⟩
              natiso2G-to-== (unit-wkmaghom-r (grphom-forg idfη)) ◃∙
              ap (λ m → idfη ∘2G m) (natiso2G-to-== (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))) ◃∙
              natiso2G-to-== (assoc-wkmaghom (grphom-forg idfη) (grphom-forg idfη) (grphom-forg idfη)) ◃∎ ∎ₛ
