{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NConnected
open import lib.types.Pointed
open import lib.types.PtdMap-conv
open import AdjEq
open import 2Grp
open import 2Semigroup
open import 2SGrpMap
open import NatIso
open import 2GrpMap
open import 2GrpMap-conv
open import 2GrpSIP
open import 2Grp-bc
open import Ptd-bc

module AdjEq-exmps where

open Adjequiv

-- an equivalence of pointed types is an adjoint equivalence
module _ {i} {X : Ptd02 i} where

  abstract
    ⊙≃-to-adjeq : {Y : Ptd i} ((φ , _) : fst X ⊙≃ Y) {c : is-connected 0 (de⊙ Y)} {t : has-level 2 (de⊙ Y)}
      → Adjequiv {a = X} {b = (Y , c , t)} φ
    ⊙≃-to-adjeq = 
      ⊙≃-ind {X = fst X}
        (λ Y (φ , _) → {c : is-connected 0 (de⊙ Y)} {t : has-level 2 (de⊙ Y)} → Adjequiv {a = X} {b = (Y , c , t)} φ)
        adj-str
        where
          adj-str : {c : is-connected 0 (de⊙ (fst X))} {t : has-level 2 (de⊙ (fst X))}
            → Adjequiv {a = X} {b =  ((fst X) , c , t)} (⊙idf (fst X))
          inv adj-str = ⊙idf (fst X)
          eta adj-str = idp
          eps adj-str = idp
          coher-map adj-str = =ₛ-out $
            ⊙-comp-to-== (⊙∘-runit (⊙idf (fst X))) ◃∙
            ⊙-comp-to-== (⊙∘-α-comp (⊙idf (fst X)) (⊙idf (fst X)) (⊙idf (fst X))) ◃∎
              =ₛ⟨ !ₛ (⊙∘-conv (⊙∘-runit (⊙idf (fst X))) (⊙∘-α-comp (⊙idf (fst X)) (⊙idf (fst X)) (⊙idf (fst X)))) ⟩
            ⊙-comp-to-== (⊙∘-runit (⊙idf (fst X)) ∙⊙∼ ⊙∘-α-comp (⊙idf (fst X)) (⊙idf (fst X)) (⊙idf (fst X))) ◃∎
              =ₛ₁⟨ ap ⊙-comp-to-== (⊙→∼-to-== ((λ _ → idp) , idp)) ⟩
            ⊙-comp-to-== (⊙∘-lunit (⊙idf (fst X))) ◃∎
              =ₛ₁⟨ ! (∙-unit-r (⊙-comp-to-== (⊙∘-lunit (⊙idf (fst X))))) ⟩
            (⊙-comp-to-== (⊙∘-lunit (⊙idf (fst X))) ∙ idp) ◃∎ ∎ₛ
          coher-inv adj-str = =ₛ-out $
            (⊙-comp-to-== (⊙∘-lunit (⊙idf (fst X))) ∙ idp) ◃∎
              =ₛ₁⟨ ∙-unit-r (⊙-comp-to-== (⊙∘-lunit (⊙idf (fst X)))) ⟩
            ⊙-comp-to-== (⊙∘-lunit (⊙idf (fst X))) ◃∎
              =ₛ₁⟨ ap ⊙-comp-to-== (⊙→∼-to-== ((λ _ → idp) , idp)) ⟩
            ⊙-comp-to-== (⊙∘-runit (⊙idf (fst X)) ∙⊙∼ ⊙∘-α-comp (⊙idf (fst X)) (⊙idf (fst X)) (⊙idf (fst X))) ◃∎
              =ₛ⟨ ⊙∘-conv (⊙∘-runit (⊙idf (fst X))) (⊙∘-α-comp (⊙idf (fst X)) (⊙idf (fst X)) (⊙idf (fst X))) ⟩
           ⊙-comp-to-== (⊙∘-runit (⊙idf (fst X))) ◃∙
           ⊙-comp-to-== (⊙∘-α-comp (⊙idf (fst X)) (⊙idf (fst X)) (⊙idf (fst X))) ◃∎ ∎ₛ 

-- an equivalence of 2-groups is an adjoint equivalence
module _ {i} {G₁ : Type i} {η₁ : CohGrp G₁} where

  open CohGrpHom

  abstract
    2g≃-to-adjeq : {(_ , η₂) : 2Grp-tot i} →
      (((map , _) , σ) : η₁ 2g≃ η₂) → Adjequiv {{ξ = 2grp-bicat-instance}} (cohgrphom {{η₁}} {{η₂}} map {{σ}})
    2g≃-to-adjeq = 
      2grphom-ind
        (λ ((_ , η₂) : 2Grp-tot i) (((map , _) , σ) : η₁ 2g≃ η₂)
          → Adjequiv (cohgrphom {{η₁}} {{η₂}} map {{σ}}))
        (adj-str {{η₁}})
        where
          adj-str : {{η : CohGrp G₁}} → Adjequiv {{ξ = 2grp-bicat-instance}} (cohgrphom {{η}} {{η}} (idf G₁) {{idf2G {{η}}}})
          map (inv adj-str) = idf G₁
          str (inv adj-str) = idf2G
          eta adj-str = natiso2G-to-== (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))
          eps adj-str = natiso2G-to-== (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))
          coher-map (adj-str {{η}}) = let idfη = cohgrphom (idf G₁) {{idf2G}} in
            =ₛ-out $
              natiso2G-to-== (unit-wksgrphom-r (grphom-forg idfη)) ◃∙
              ap (λ m → idfη ∘2G m)
                (natiso2G-to-== (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))) ◃∙
              natiso2G-to-== (assoc-wksgrphom (grphom-forg idfη) (grphom-forg (inv adj-str)) (grphom-forg idfη)) ◃∎
                =ₛ₁⟨ 1 & 1 & ! (whisk2G-conv-l (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))) ⟩
              natiso2G-to-== (unit-wksgrphom-r (grphom-forg idfη)) ◃∙
              natiso2G-to-== (natiso-whisk-l {{η₂ = sgrp η}} {ν₁ = grphom-forg idfη} (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))) ◃∙
              natiso2G-to-== (assoc-wksgrphom (grphom-forg idfη) (grphom-forg (inv adj-str)) (grphom-forg idfη)) ◃∎
                =ₛ⟨ !ₛ (
                      ∘2G-conv-tri
                        (unit-wksgrphom-r (grphom-forg idfη))
                        (natiso-whisk-l {{η₂ = sgrp η}} {ν₁ = grphom-forg idfη} (cohgrpnatiso (λ _ → idp) (λ _ _ → idp)))
                        (assoc-wksgrphom (grphom-forg idfη) (grphom-forg (inv adj-str)) (grphom-forg idfη))) ⟩
              natiso2G-to-==
                (assoc-wksgrphom (grphom-forg idfη) (wksgrphom (idf G₁) (λ x y → idp)) (grphom-forg idfη)
                  natiso-∘
                natiso-whisk-l {{η₂ = sgrp η}} {ν₁ = grphom-forg idfη} (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))
                  natiso-∘
                unit-wksgrphom-r (grphom-forg idfη)) ◃∎
                =ₛ₁⟨ ap natiso2G-to-== (natiso∼-to-== (λ _ → idp)) ⟩
              natiso2G-to-==
                (natiso-whisk-r (cohgrpnatiso (λ _ → idp) (λ _ _ → idp)) natiso-∘ unit-wksgrphom-l (grphom-forg idfη)) ◃∎
                =ₛ⟨ ∘2G-conv
                      (unit-wksgrphom-l (grphom-forg idfη))
                      (natiso-whisk-r {{η₂ = sgrp η}} {μ = grphom-forg idfη} (cohgrpnatiso (λ _ → idp) (λ _ _ → idp)))  ⟩
              natiso2G-to-== (unit-wksgrphom-l (grphom-forg idfη)) ◃∙
              natiso2G-to-== (natiso-whisk-r {{η₂ = sgrp η}} {μ = grphom-forg idfη} (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))) ◃∎
                =ₛ₁⟨ 1 & 1 & whisk2G-conv-r (cohgrpnatiso (λ _ → idp) (λ _ _ → idp)) ⟩
              natiso2G-to-== (unit-wksgrphom-l (grphom-forg idfη)) ◃∙
              ap (λ m → m ∘2G idfη)
                (natiso2G-to-== (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))) ◃∎ ∎ₛ            
          coher-inv (adj-str {{η}}) = let idfη = cohgrphom (idf G₁) {{idf2G}} in
            =ₛ-out $
              natiso2G-to-== (unit-wksgrphom-l (grphom-forg idfη)) ◃∙
              ap (λ m → m ∘2G idfη) (natiso2G-to-== (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))) ◃∎
                =ₛ₁⟨ 1 & 1 & ! (whisk2G-conv-r (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))) ⟩
              natiso2G-to-== (unit-wksgrphom-l (grphom-forg idfη)) ◃∙
              natiso2G-to-== (natiso-whisk-r {{η₂ = sgrp η}} {μ = grphom-forg idfη} (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))) ◃∎
                =ₛ⟨ !ₛ
                      (∘2G-conv (unit-wksgrphom-l (grphom-forg idfη)) (natiso-whisk-r {{η₂ = sgrp η}} {μ = grphom-forg idfη}
                        (cohgrpnatiso (λ _ → idp) (λ _ _ → idp)))) ⟩
              natiso2G-to-== (natiso-whisk-r (cohgrpnatiso (λ _ → idp) (λ _ _ → idp)) natiso-∘ unit-wksgrphom-l (grphom-forg idfη)) ◃∎
                =ₛ₁⟨ ap natiso2G-to-== (natiso∼-to-== (λ _ → idp)) ⟩
              natiso2G-to-== (
                assoc-wksgrphom (grphom-forg idfη) (grphom-forg idfη) (grphom-forg idfη)
                  natiso-∘
                natiso-whisk-l {{η₂ = sgrp η}} {ν₁ = grphom-forg idfη} (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))
                  natiso-∘
                unit-wksgrphom-r (grphom-forg idfη)) ◃∎
                =ₛ⟨ ∘2G-conv-tri
                      (unit-wksgrphom-r (grphom-forg idfη))
                      (natiso-whisk-l {{η₂ = sgrp η}} {ν₁ = grphom-forg idfη} (cohgrpnatiso (λ _ → idp) (λ _ _ → idp)))
                      (assoc-wksgrphom (grphom-forg idfη) (grphom-forg idfη) (grphom-forg idfη)) ⟩
              natiso2G-to-== (unit-wksgrphom-r (grphom-forg idfη)) ◃∙
              natiso2G-to-== (natiso-whisk-l {{η₂ = sgrp η}} {ν₁ = grphom-forg idfη} (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))) ◃∙
              natiso2G-to-== (assoc-wksgrphom (grphom-forg idfη) (grphom-forg idfη) (grphom-forg idfη)) ◃∎
                =ₛ₁⟨ 1 & 1 & whisk2G-conv-l (cohgrpnatiso (λ _ → idp) (λ _ _ → idp)) ⟩
              natiso2G-to-== (unit-wksgrphom-r (grphom-forg idfη)) ◃∙
              ap (λ m → idfη ∘2G m) (natiso2G-to-== (cohgrpnatiso (λ _ → idp) (λ _ _ → idp))) ◃∙
              natiso2G-to-== (assoc-wksgrphom (grphom-forg idfη) (grphom-forg idfη) (grphom-forg idfη)) ◃∎ ∎ₛ
