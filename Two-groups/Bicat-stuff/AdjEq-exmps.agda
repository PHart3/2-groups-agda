{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NConnected
open import lib.types.Pointed
open import lib.types.PtdMap-conv
open import AdjEq
open import 2SGrpMap
open import 2Semigroup
open import 2Grp
open import 2GrpMap
open import 2GrpSIP
open import 2Grp-bc
open import Ptd-bc
open import Univ-bc

-- adjoint equivalences in our two specific settings of interest

module AdjEq-exmps where

open Adjequiv

module _ {i} {X : Ptd02 i} where

  adjeq-to-⊙≃ : {Y : Ptd02 i} → AdjEquiv (Ptd02-bicat i) X Y →  fst X ⊙≃ fst Y
  fst (adjeq-to-⊙≃ φ) = fst φ
  is-equiv.g (snd (adjeq-to-⊙≃ (φ , ae))) = fst (inv ae)
  is-equiv.f-g (snd (adjeq-to-⊙≃ (φ , ae))) b = ! (fst (==-to-⊙-crd∼  (eps ae)) b)
  is-equiv.g-f (snd (adjeq-to-⊙≃ (φ , ae))) a = ! (fst (==-to-⊙-crd∼  (eta ae)) a)
  is-equiv.adj (snd (adjeq-to-⊙≃ (φ , ae))) a = ap-! (fst φ) (fst (==-to-⊙-crd∼ (eta ae)) a) ∙ ! (!-∙ _ idp) ∙ ap ! (app= (ap fst lemma) a)
    where abstract
      lemma : (⊙∘-runit φ ∙⊙∼ ⊙∘-post φ (==-to-⊙-crd∼ (eta ae)) ∙⊙∼ ⊙∘-α-comp φ (inv ae) φ) == (⊙∘-lunit φ ∙⊙∼ ⊙∘-pre φ (==-to-⊙-crd∼ (eps ae)))
      lemma =
        ⊙∘-runit φ ∙⊙∼ ⊙∘-post φ (==-to-⊙-crd∼ (eta ae)) ∙⊙∼ ⊙∘-α-comp φ (inv ae) φ
          =⟨ ap3 (λ h₁ h₂ h₃ → h₁ ∙⊙∼ h₂ ∙⊙∼ h₃)
               (! (<–-inv-r ⊙-crd∼-==-≃ (⊙∘-runit φ))) (! (==-to-⊙-crd∼-whisk-l (eta ae))) (! (<–-inv-r ⊙-crd∼-==-≃ (⊙∘-α-comp φ (inv ae) φ))) ⟩
        ==-to-⊙-crd∼ (⊙-crd∼-to-== (⊙∘-runit φ)) ∙⊙∼
        ==-to-⊙-crd∼  (ap (λ f → φ ⊙∘ f) (eta ae)) ∙⊙∼
        ==-to-⊙-crd∼  (⊙-crd∼-to-== (⊙∘-α-comp φ (inv ae) φ))
          =⟨ ! (==-to-⊙-crd∼-∙2 (⊙-crd∼-to-== (⊙∘-runit φ)) (ap (λ f → φ ⊙∘ f) (eta ae)) (⊙-crd∼-to-== (⊙∘-α-comp φ (inv ae) φ))) ⟩
        ==-to-⊙-crd∼ (⊙-crd∼-to-== (⊙∘-runit φ) ∙ ap (λ f → φ ⊙∘ f) (eta ae) ∙ ⊙-crd∼-to-== (⊙∘-α-comp φ (inv ae) φ))
          =⟨ ap ==-to-⊙-crd∼ (coher-map ae) ⟩
        ==-to-⊙-crd∼ (⊙-crd∼-to-== (⊙∘-lunit φ) ∙ ap (λ m → m ⊙∘ φ) (eps ae))
          =⟨ ==-to-⊙-crd∼-∙ (⊙-crd∼-to-== (⊙∘-lunit φ)) (ap (λ m → m ⊙∘ φ) (eps ae)) ⟩
        ==-to-⊙-crd∼ (⊙-crd∼-to-== (⊙∘-lunit φ)) ∙⊙∼ ==-to-⊙-crd∼ (ap (λ m → m ⊙∘ φ) (eps ae))
          =⟨ ap2 _∙⊙∼_ (<–-inv-r ⊙-crd∼-==-≃ (⊙∘-lunit φ)) (==-to-⊙-crd∼-whisk-r (eps ae)) ⟩
        (⊙∘-lunit φ ∙⊙∼ ⊙∘-pre φ (==-to-⊙-crd∼ (eps ae))) =∎
        
  -- an equivalence of pointed types is an adjoint equivalence
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

open CohGrpHom

module _ {i} {G₁ : Type i} {{η₁ : CohGrp G₁}} where

  open WkSGrpNatIso

  adjeq-to-2g≃ : {G₂ : Type i} {{η₂ : CohGrp G₂}} → AdjEquiv (2grp-bicat i) (_ , η₁) (_ , η₂) → η₁ 2g≃ η₂
  fst (fst (adjeq-to-2g≃ (f , ae))) = map f
  is-equiv.g (snd (fst (adjeq-to-2g≃ (f , ae)))) = map (inv ae)
  is-equiv.f-g (snd (fst (adjeq-to-2g≃ (f , ae)))) b = ! (θ (natiso2G-from-== (eps ae)) b)
  is-equiv.g-f (snd (fst (adjeq-to-2g≃ (f , ae)))) a = ! (θ (natiso2G-from-== (eta ae)) a)
  is-equiv.adj (snd (fst (adjeq-to-2g≃ {{η₂}} (f , ae)))) a = ap-! (map f) (θ (natiso2G-from-== (eta ae)) a) ∙ ! (!-∙ _ idp) ∙ ap ! (app= (ap θ lemma) a)
    where abstract
      lemma :
        assoc-wksgrphom (grphom-forg f) (grphom-forg (inv ae)) (grphom-forg f) natiso-∘
        natiso-whisk-l {μ = grphom-forg f} (natiso2G-from-== (eta ae)) natiso-∘
        unit-wksgrphom-r (grphom-forg f)
          ==
        natiso-whisk-r (natiso2G-from-== (eps ae)) natiso-∘ unit-wksgrphom-l (grphom-forg f)
      lemma =
        assoc-wksgrphom (grphom-forg f) (grphom-forg (inv ae)) (grphom-forg f) natiso-∘
        natiso-whisk-l {μ = grphom-forg f} (natiso2G-from-== (eta ae)) natiso-∘
        unit-wksgrphom-r (grphom-forg f)
          =⟨ ap3 (λ h₁ h₂ h₃ → h₁ natiso-∘ h₂ natiso-∘ h₃)
               (! (<–-inv-r natiso2G-==-≃ (assoc-wksgrphom (grphom-forg f) (grphom-forg (inv ae)) (grphom-forg f))))
               (! (natiso2G-from-==-whisk-l {{η₁ = η₁}} {{η₂ = η₁}} {{η₃ = η₂}} {h = f} (eta ae)))
               (! (<–-inv-r natiso2G-==-≃ (unit-wksgrphom-r (grphom-forg f)))) ⟩
        natiso2G-from-== (natiso2G-to-== (assoc-wksgrphom (grphom-forg f) (grphom-forg (inv ae)) (grphom-forg f))) natiso-∘
        natiso2G-from-== (ap (λ m → f ∘2G m) (eta ae)) natiso-∘
        natiso2G-from-== (natiso2G-to-== (unit-wksgrphom-r (grphom-forg f)))
          =⟨ ! (natiso2G-from-==-∙2
                 (natiso2G-to-== (unit-wksgrphom-r (grphom-forg f)))
                 (ap (λ m → f ∘2G m) (eta ae))
                 (natiso2G-to-== (assoc-wksgrphom (grphom-forg f) (grphom-forg (inv ae)) (grphom-forg f)))) ⟩
        natiso2G-from-== (
          natiso2G-to-== (unit-wksgrphom-r (grphom-forg f)) ∙
          ap (λ m → f ∘2G m) (eta ae) ∙
          natiso2G-to-== (assoc-wksgrphom (grphom-forg f) (grphom-forg (inv ae)) (grphom-forg f)))
          =⟨ ap natiso2G-from-== (coher-map ae) ⟩
        natiso2G-from-== (natiso2G-to-== (unit-wksgrphom-l (grphom-forg f)) ∙ ap (λ m → m ∘2G f) (eps ae))
          =⟨ natiso2G-from-==-∙ (natiso2G-to-== (unit-wksgrphom-l (grphom-forg f))) (ap (λ m → m ∘2G f) (eps ae)) ⟩
        natiso2G-from-== (ap (λ m → m ∘2G f) (eps ae)) natiso-∘ natiso2G-from-== (natiso2G-to-== (unit-wksgrphom-l (grphom-forg f)))
          =⟨ ap2 _natiso-∘_
               (natiso2G-from-==-whisk-r {{η₁ = η₂}} {{η₂ = η₁}} {{η₃ = η₁}} {h = f} (eps ae))
               (<–-inv-r natiso2G-==-≃ (unit-wksgrphom-l (grphom-forg f))) ⟩
        (natiso-whisk-r (natiso2G-from-== (eps ae)) natiso-∘ unit-wksgrphom-l (grphom-forg f)) =∎
  snd (adjeq-to-2g≃ (f , ae)) = str f

-- an equivalence of 2-groups is an adjoint equivalence
module _ {i} {G₁ : Type i} {η₁ : CohGrp G₁} where

  abstract
    2g≃-to-adjeq : {(_ , η₂) : 2Grp-tot i} →
      (((map , _) , σ) : η₁ 2g≃ η₂) → Adjequiv {{2grp-bicat-instance}} (cohgrphom {{η₁}} {{η₂}} map {{σ}})
    2g≃-to-adjeq = 
      2grphom-ind
        (λ ((_ , η₂) : 2Grp-tot i) (((map , _) , σ) : η₁ 2g≃ η₂)
          → Adjequiv (cohgrphom {{η₁}} {{η₂}} map {{σ}}))
        (snd (AdjEq-id₁ {{2grp-bicat-instance}}))
