{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NConnected
open import lib.types.Pointed
open import lib.types.PtdMap-conv
open import AdjEq
open import 2Grp
open import 2GrpSIP
open import 2Grp-bc
open import Ptd-bc
open import Univ-bc

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
            ⊙-crd∼-to-== (⊙∘-runit (⊙idf (fst X))) ◃∙
            ⊙-crd∼-to-== (⊙∘-α-comp (⊙idf (fst X)) (⊙idf (fst X)) (⊙idf (fst X))) ◃∎
              =ₛ⟨ !ₛ (⊙∘-conv (⊙∘-runit (⊙idf (fst X))) (⊙∘-α-comp (⊙idf (fst X)) (⊙idf (fst X)) (⊙idf (fst X)))) ⟩
            ⊙-crd∼-to-== (⊙∘-runit (⊙idf (fst X)) ∙⊙∼ ⊙∘-α-comp (⊙idf (fst X)) (⊙idf (fst X)) (⊙idf (fst X))) ◃∎
              =ₛ₁⟨ ap ⊙-crd∼-to-== (⊙→∼-to-== ((λ _ → idp) , idp)) ⟩
            ⊙-crd∼-to-== (⊙∘-lunit (⊙idf (fst X))) ◃∎
              =ₛ₁⟨ ! (∙-unit-r (⊙-crd∼-to-== (⊙∘-lunit (⊙idf (fst X))))) ⟩
            (⊙-crd∼-to-== (⊙∘-lunit (⊙idf (fst X))) ∙ idp) ◃∎ ∎ₛ
          coher-inv adj-str = =ₛ-out $              
            ⊙-crd∼-to-== (⊙∘-runit (⊙idf (fst X))) ◃∙
            ⊙-crd∼-to-== (⊙∘-α-comp (⊙idf (fst X)) (⊙idf (fst X)) (⊙idf (fst X))) ◃∎
              =ₛ⟨ !ₛ (⊙∘-conv (⊙∘-runit (⊙idf (fst X))) (⊙∘-α-comp (⊙idf (fst X)) (⊙idf (fst X)) (⊙idf (fst X)))) ⟩
            ⊙-crd∼-to-== (⊙∘-runit (⊙idf (fst X)) ∙⊙∼ ⊙∘-α-comp (⊙idf (fst X)) (⊙idf (fst X)) (⊙idf (fst X))) ◃∎
              =ₛ₁⟨ ! (ap ⊙-crd∼-to-== (⊙→∼-to-== ((λ _ → idp) , idp))) ⟩
            ⊙-crd∼-to-== (⊙∘-lunit (⊙idf (fst X))) ◃∎
              =ₛ₁⟨ ! (∙-unit-r (⊙-crd∼-to-== (⊙∘-lunit (⊙idf (fst X))))) ⟩
            (⊙-crd∼-to-== (⊙∘-lunit (⊙idf (fst X))) ∙ idp) ◃∎ ∎ₛ
            
-- an equivalence of 2-groups is an adjoint equivalence
module _ {i} {G₁ : Type i} {η₁ : CohGrp G₁} where

  open CohGrpHom

  abstract
    2g≃-to-adjeq : {(_ , η₂) : 2Grp-tot i} →
      (((map , _) , σ) : η₁ 2g≃ η₂) → Adjequiv {{2grp-bicat-instance}} (cohgrphom {{η₁}} {{η₂}} map {{σ}})
    2g≃-to-adjeq = 
      2grphom-ind
        (λ ((_ , η₂) : 2Grp-tot i) (((map , _) , σ) : η₁ 2g≃ η₂)
          → Adjequiv (cohgrphom {{η₁}} {{η₂}} map {{σ}}))
        (snd (AdjEq-id₁ {{2grp-bicat-instance}}))
