{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import Bicategory
open import Bicat-coher
open import AdjEqv
open import WkEqv-bc

-- some relations between weak equivalences and adjoint equivalences

module WkEqv-bc-ops {i j} {B₀ : Type i} where

open BicatStr {{...}}

module _ {{ξB : BicatStr j B₀}} where

  open Wkequiv-bc
  open Adjequiv

  adjeqv-frg : {a b : B₀} → AdjEquiv ξB a b → WkEquiv-bc ξB a b
  fst (adjeqv-frg (f , ae)) = f
  snd (adjeqv-frg (f , ae)) = Wk-eqv (inv ae) (eta ae) (eps ae)

  -- every weak equivalence can be promoted to an adjoint one

  module _ {a b : B₀} ((f , we) : WkEquiv-bc ξB a b) where

    abstract

      wkeqv-refine0 :
        ρ f ◃∙
        ap (λ m → f ◻ m) (eta we) ◃∙
        α f (inv we) f ◃∎
          =ₛ
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ! (α f (inv we) f) ◃∙
        ap (λ m → f ◻ m)
          (ap (λ m → m ◻ f) (lamb (inv we)) ∙ ! (α (id₁ _) (inv we) f) ∙ ! (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ! (ap (λ m → f ◻ m) (α (inv we) f (id₁ _))) ◃∙
        α f (inv we) (f ◻ id₁ _) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
      wkeqv-refine0 = 
        ρ f ◃∙
        ap (λ m → f ◻ m) (eta we) ◃∙
        α f (inv we) f ◃∎
          =ₛ⟨ =ₛ-in (! (ap-idf-idp (ρ f ∙  ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f))) ⟩
        ap (λ m → m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        idp ◃∎
          =ₛ⟨ 1 & 1 & =ₛ-in (=ₛ-out (trig-lamb-bc-rot2 (f ◻ inv we) f)) ⟩
        ap (λ m → m) (ρ f ∙  ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        lamb (⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 0 & 2 & homotopy-naturality _ _ lamb (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ⟩
        lamb f ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₑ⟨ 0 & 1 & (lamb f ◃∙ idp ◃∎) % =ₛ-in (! (∙-unit-r (lamb f))) ⟩
        lamb f ◃∙
        idp ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₑ⟨ 1 & 1 & (ap (λ m → m ◻ f) (eps we) ◃∙ idp ◃∙ ! (ap (λ m → m ◻ f) (eps we)) ◃∎)
            % =ₛ-in (! (!-inv-r (ap (λ m → m ◻ f) (eps we)))) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        idp ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₑ⟨ 2 & 1 & (! (α f (inv we) f) ◃∙ idp ◃∙ idp ◃∙ α f (inv we) f ◃∎) % =ₛ-in (! (!-inv-l (α f (inv we) f))) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ! (α f (inv we) f) ◃∙
        idp ◃∙
        idp ◃∙
        α f (inv we) f ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₑ⟨ 4 & 1 & (ap (λ m → f ◻ m) (ρ (inv we ◻ f) ∙ ! (α (inv we) f (id₁ _)) ∙ ! (ap (λ m → inv we ◻ m) (ρ f))) ◃∎)
            % =ₛ-in (ap (ap (λ m → f ◻ m)) (! (=ₛ-out (trig-ρ-bc-rot-pre (inv we) f)))) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ! (α f (inv we) f) ◃∙
        idp ◃∙
        ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙ ! (α (inv we) f (id₁ _)) ∙ ! (ap (λ m → inv we ◻ m) (ρ f))) ◃∙
        α f (inv we) f ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 4 & 1 & ap-∙!!◃ (λ m → f ◻ m) (ρ (inv we ◻ f)) (α (inv we) f (id₁ _)) (ap (λ m → inv we ◻ m) (ρ f)) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ! (α f (inv we) f) ◃∙
        idp ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ! (ap (λ m → f ◻ m) (α (inv we) f (id₁ _))) ◃∙
        ! (ap (λ m → f ◻ m) (ap (λ m → inv we ◻ m) (ρ f))) ◃∙
        α f (inv we) f ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ₁⟨ 6 & 1 & ap ! (∘-ap (λ m → f ◻ m) (λ m → inv we ◻ m) (ρ f)) ⟩ 
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ! (α f (inv we) f) ◃∙
        idp ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ! (ap (λ m → f ◻ m) (α (inv we) f (id₁ _))) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ inv we ◻ m) (ρ f)) ◃∙
        α f (inv we) f ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 6 & 2 & !ₛ (homotopy-naturality-!ap (λ m → α f (inv we) m) (ρ f)) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ! (α f (inv we) f) ◃∙
        idp ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ! (ap (λ m → f ◻ m) (α (inv we) f (id₁ _))) ◃∙
        α f (inv we) (f ◻ id₁ _) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₑ⟨ 3 & 1 &
            (ap (λ m → f ◻ m)
              (ap (λ m → m ◻ f) (lamb (inv we)) ∙ ! (α (id₁ _) (inv we) f) ∙ ! (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∎)
            % =ₛ-in (ap (ap (λ m → f ◻ m)) (! (=ₛ-out (trig-lamb-bc-rot (inv we) f)))) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ! (α f (inv we) f) ◃∙
        ap (λ m → f ◻ m)
          (ap (λ m → m ◻ f) (lamb (inv we)) ∙ ! (α (id₁ _) (inv we) f) ∙ ! (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ! (ap (λ m → f ◻ m) (α (inv we) f (id₁ _))) ◃∙
        α f (inv we) (f ◻ id₁ _) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎ ∎ₛ

      wkeqv-refine1 :
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ! (α f (inv we) f) ◃∙
        ap (λ m → f ◻ m)
          (ap (λ m → m ◻ f) (lamb (inv we)) ∙ ! (α (id₁ _) (inv we) f) ∙ ! (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ! (ap (λ m → f ◻ m) (α (inv we) f (id₁ _))) ◃∙
        α f (inv we) (f ◻ id₁ _) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        α f (inv we ◻ f) (inv we ◻ f) ◃∙
        ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv we ◻ f) (α f (inv we) f) ◃∙
        idp ◃∙
        ! (α (f ◻ inv we) f (inv we ◻ f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
      wkeqv-refine1 =
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ! (α f (inv we) f) ◃∙
        ap (λ m → f ◻ m)
          (ap (λ m → m ◻ f) (lamb (inv we)) ∙ ! (α (id₁ _) (inv we) f) ∙ ! (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ! (ap (λ m → f ◻ m) (α (inv we) f (id₁ _))) ◃∙
        α f (inv we) (f ◻ id₁ _) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 3 & 1 & ap-∙!!◃ (λ m → f ◻ m)
            (ap (λ m → m ◻ f) (lamb (inv we))) (α (id₁ _) (inv we) f) (lamb (⟦ ξB ⟧ inv we ◻ f)) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ! (α f (inv we) f) ◃∙
        ap (λ m → f ◻ m) (ap (λ m → m ◻ f) (lamb (inv we))) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ! (ap (λ m → f ◻ m) (α (inv we) f (id₁ _))) ◃∙
        α f (inv we) (f ◻ id₁ _) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ₁⟨ 3 & 1 & ∘-ap (λ m → f ◻ m) (λ m → m ◻ f) (lamb (inv we)) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ! (α f (inv we) f) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ m ◻ f) (lamb (inv we)) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ! (ap (λ m → f ◻ m) (α (inv we) f (id₁ _))) ◃∙
        α f (inv we) (f ◻ id₁ _) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 2 & 2 & homotopy-naturality-! (λ m → α f m f) (lamb (inv we)) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ m ◻ f) (lamb (inv we)) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ! (ap (λ m → f ◻ m) (α (inv we) f (id₁ _))) ◃∙
        α f (inv we) (f ◻ id₁ _) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ₁⟨ 2 & 1 & ap-∘ (λ m → m ◻ f) (λ m → f ◻ m) (lamb (inv we)) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ! (ap (λ m → f ◻ m) (α (inv we) f (id₁ _))) ◃∙
        α f (inv we) (f ◻ id₁ _) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₑ⟨ 7 & 2 & (! (ap (λ m → f ◻ m) (α (inv we) f (id₁ _))) ∙ α f (inv we) (f ◻ id₁ _)) ◃∎ % =ₛ-in idp ⟩ 
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        (! (ap (λ m → f ◻ m) (α (inv we) f (id₁ _))) ∙ α f (inv we) (f ◻ id₁ _)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 7 & 1 &
            apCommSq2◃-rev (λ k → ! (ap (λ m → f ◻ m) (α (inv we) f k)) ∙ α f (inv we) (⟦ ξB ⟧ f ◻ k)) (eta we) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        (! (ap (λ m → f ◻ m) (α (inv we) f (inv we ◻ f))) ∙ α f (inv we) (⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ inv we ◻ f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₑ⟨ 8 & 1 &
            (α f (inv we ◻ f) (inv we ◻ f) ◃∙
            ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv we ◻ f) (α f (inv we) f) ◃∙
            idp ◃∙
            ! (α (f ◻ inv we) f (inv we ◻ f)) ◃∎)
            % =ₛ-in (=ₛ-out (pent-bc◃-rot6 (inv we ◻ f) f (inv we) f)) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        α f (inv we ◻ f) (inv we ◻ f) ◃∙
        ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv we ◻ f) (α f (inv we) f) ◃∙
        idp ◃∙
        ! (α (f ◻ inv we) f (inv we ◻ f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎ ∎ₛ

      wkeqv-refine2 :
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        α f (inv we ◻ f) (inv we ◻ f) ◃∙
        ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv we ◻ f) (α f (inv we) f) ◃∙
        idp ◃∙
        ! (α (f ◻ inv we) f (inv we ◻ f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        ap (λ m → f ◻ m) (α (inv we ◻ f) (inv we) f) ◃∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (α (f ◻ inv we) (f ◻ inv we) f) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (α f (inv we) f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
      wkeqv-refine2 =
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        α f (inv we ◻ f) (inv we ◻ f) ◃∙
        ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv we ◻ f) (α f (inv we) f) ◃∙
        idp ◃∙
        ! (α (f ◻ inv we) f (inv we ◻ f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₑ⟨ 10 & 1 &
            (α (⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ f) (inv we) f ◃∙ ! (α (⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ f) (inv we) f) ◃∎)
            % =ₛ-in (! (!-inv-r (α (⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ f) (inv we) f))) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        α f (inv we ◻ f) (inv we ◻ f) ◃∙
        ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv we ◻ f) (α f (inv we) f) ◃∙
        α (⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ f) (inv we) f ◃∙
        ! (α (⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ f) (inv we) f) ◃∙
        ! (α (f ◻ inv we) f (inv we ◻ f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 8 & 1 & pent-bc◃-rot5 f (inv we) (inv we ◻ f) f ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        ap (λ m → f ◻ m) (α (inv we ◻ f) (inv we) f) ◃∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (α f (inv we ◻ f) (inv we)) ◃∙
        ! (α (⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ inv we ◻ f) (inv we) f) ◃∙
        ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv we ◻ f) (α f (inv we) f) ◃∙
        α (⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ f) (inv we) f ◃∙
        ! (α (⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ f) (inv we) f) ◃∙
        ! (α (f ◻ inv we) f (inv we ◻ f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 11 & 3 & !ₛ (apCommSq◃ (λ m → α m (inv we) f) (α f (inv we) f)) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        ap (λ m → f ◻ m) (α (inv we ◻ f) (inv we) f) ◃∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (α f (inv we ◻ f) (inv we)) ◃∙
        ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ m ◻ inv we ◻ f) (α f (inv we) f) ◃∙
        ! (α (⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ f) (inv we) f) ◃∙
        ! (α (f ◻ inv we) f (inv we ◻ f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ₁⟨ 11 & 1 & ap-∘ (λ m → m ◻ f) (λ m → m ◻ inv we) (α f (inv we) f) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        ap (λ m → f ◻ m) (α (inv we ◻ f) (inv we) f) ◃∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (α f (inv we ◻ f) (inv we)) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → m ◻ inv we) (α f (inv we) f)) ◃∙
        ! (α (⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ f) (inv we) f) ◃∙
        ! (α (f ◻ inv we) f (inv we ◻ f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 10 & 2 & ap-seq-=ₛ (λ m → m ◻ f) (!ₛ (pent-bc◃-rot4 (inv we) f (inv we) f)) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        ap (λ m → f ◻ m) (α (inv we ◻ f) (inv we) f) ◃∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ap (λ m → m ◻ f) (α (f ◻ inv we) f (inv we)) ◃∙
        ! (α (⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ f) (inv we) f) ◃∙
        ! (α (f ◻ inv we) f (inv we ◻ f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 12 & 3 & !ₛ (pent-bc◃-rot3 f (inv we) f (f ◻ inv we)) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        ap (λ m → f ◻ m) (α (inv we ◻ f) (inv we) f) ◃∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (α (f ◻ inv we) (f ◻ inv we) f) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (α f (inv we) f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎ ∎ₛ

      wkeqv-refine3 :
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        ap (λ m → f ◻ m) (α (inv we ◻ f) (inv we) f) ◃∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (α (f ◻ inv we) (f ◻ inv we) f) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (α f (inv we) f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        (! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ∙
        α (f ◻ inv we) (f ◻ inv we) f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
      wkeqv-refine3 = 
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        ap (λ m → f ◻ m) (α (inv we ◻ f) (inv we) f) ◃∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (α (f ◻ inv we) (f ◻ inv we) f) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (α f (inv we) f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ₁⟨ 7 & 1 & ap-∘ (λ m → f ◻ m) (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → f ◻ m) (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we)) ◃∙
        ap (λ m → f ◻ m) (α (inv we ◻ f) (inv we) f) ◃∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (α (f ◻ inv we) (f ◻ inv we) f) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (α f (inv we) f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ₁⟨ 14 & 1 & ap ! (ap-∘ (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (λ m → f ◻ m) (eta we)) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → f ◻ m) (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we)) ◃∙
        ap (λ m → f ◻ m) (α (inv we ◻ f) (inv we) f) ◃∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (α (f ◻ inv we) (f ◻ inv we) f) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (α f (inv we) f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ap (λ m → f ◻ m) (eta we))) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 6 & 4 & ap-∙2∙◃ (λ m → f ◻ m)
            (ρ (inv we ◻ f)) (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we))
            (α (inv we ◻ f) (inv we) f) (α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (α (f ◻ inv we) (f ◻ inv we) f) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (α f (inv we) f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ap (λ m → f ◻ m) (eta we))) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 9 & 4 & !-ap-∙2∙◃ (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m)
            (ρ f) (ap (λ m → f ◻ m) (eta we)) (α f (inv we) f) (α (f ◻ inv we) (f ◻ inv we) f) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        (! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ∙
        α (f ◻ inv we) (f ◻ inv we) f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎ ∎ₛ

      wkeqv-refine4 :
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        (! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ∙
        α (f ◻ inv we) (f ◻ inv we) f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (ap (λ m → id₁ _ ◻ m) (eta we))) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (id₁ _))) ◃∙
        ap (λ m → f ◻ m) (eta we) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we ◻ f) (eps we)) ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
      wkeqv-refine4 =
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        (! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ∙
        α (f ◻ inv we) (f ◻ inv we) f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₑ⟨ 11 & 2 &
            (ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ∙ α (id₁ _) (f ◻ inv we) f) ◃∎
            % =ₛ-in idp ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        (! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ∙
        α (f ◻ inv we) (f ◻ inv we) f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        (ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ∙
        α (id₁ _) (f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 9 & 3 & !ₛ (apCommSq◃!
            (λ m → ap (λ k → m ◻ k) (ρ f ∙ ap (λ k → f ◻ k) (eta we) ∙ α f (inv we) f) ∙ α m (f ◻ inv we) f)
            (eps we)) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we ◻ f) (eps we)) ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 5 & 1 & apCommSq2◃!-ap lamb (eta we) (λ m → f ◻ m) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (ap (λ m → id₁ _ ◻ m) (eta we))) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (id₁ _))) ◃∙
        ap (λ m → f ◻ m) (ap (λ m → m) (eta we)) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we ◻ f) (eps we)) ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ₁⟨ 7 & 1 & ap (ap (λ m → f ◻ m)) (ap-idf (eta we)) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (ap (λ m → id₁ _ ◻ m) (eta we))) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (id₁ _))) ◃∙
        ap (λ m → f ◻ m) (eta we) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we ◻ f) (eps we)) ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎ ∎ₛ

      wkeqv-refine5 :
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (ap (λ m → id₁ _ ◻ m) (eta we))) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (id₁ _))) ◃∙
        ap (λ m → f ◻ m) (eta we) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we ◻ f) (eps we)) ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ
        lamb f ◃∙
        ap (λ m → m ◻ f)
          (eps we ∙
          ap (λ m → f ◻ m) (lamb (inv we)) ∙
          ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ m ◻ inv we) (eta we) ∙
          ! (ap (λ m → f ◻ m) (α (inv we) f (inv we))) ∙
          α f (inv we) (⟦ ξB ⟧ f ◻ inv we) ∙
          ! (ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we) (eps we)) ∙
          ! (lamb (f ◻ inv we))) ◃∎
      wkeqv-refine5 =
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (ap (λ m → id₁ _ ◻ m) (eta we))) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (id₁ _))) ◃∙
        ap (λ m → f ◻ m) (eta we) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we ◻ f) (eps we)) ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ₁⟨ 6 & 1 & ap ! (ap (ap (λ m → f ◻ m)) lamb-ρ-id₁-bc) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (ap (λ m → id₁ _ ◻ m) (eta we))) ◃∙
        ! (ap (λ m → f ◻ m) (ρ (id₁ _))) ◃∙
        ap (λ m → f ◻ m) (eta we) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we ◻ f) (eps we)) ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 3 & 4 & !-ap-∙2∙◃ (λ m → f ◻ m)
            (ρ (id₁ _)) (ap (λ m → id₁ _ ◻ m) (eta we)) (α (id₁ _) (inv we) f) (α f (id₁ _ ◻ inv we) f) ⟩ 
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        (! (ap (λ m → f ◻ m) (ρ (id₁ _) ∙ ap (λ m → id₁ _ ◻ m) (eta we) ∙ α (id₁ _) (inv we) f) ∙
        α f (id₁ _ ◻ inv we) f)) ◃∙
        ap (λ m → f ◻ m) (eta we) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we ◻ f) (eps we)) ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 3 & 3 & !ₛ $
            apCommSq◃
              (λ m → ap (λ k → f ◻ k) (ρ m ∙ ap (λ k → m ◻ k) (eta we) ∙ α m (inv we) f) ∙ α f (m ◻ inv we) f)
              (eta we) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ m ◻ inv we ◻ f) (eta we) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we ◻ f) (eps we)) ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ₁⟨ 3 & 1 & ap-∘ (λ m → m ◻ f) (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ m ◻ inv we) (eta we) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ m ◻ inv we) (eta we)) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we ◻ f) (eps we)) ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ₁⟨ 6 & 1 & !-ap-∘ (λ m → m ◻ f) (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we) (eps we) ⟩ 
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ m ◻ inv we) (eta we)) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we) (eps we))) ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 1 & 7 & !ₛ (ap-seq-∙ (λ m → m ◻ f)
            (eps we ◃∙
            ap (λ m → f ◻ m) (lamb (inv we)) ◃∙
            ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ m ◻ inv we) (eta we) ◃∙
            ! (ap (λ m → f ◻ m) (α (inv we) f (inv we))) ◃∙
            α f (inv we) (⟦ ξB ⟧ f ◻ inv we) ◃∙
            ! (ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we) (eps we)) ◃∙
            ! (lamb (f ◻ inv we)) ◃∎)) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f)
          (eps we ∙
          ap (λ m → f ◻ m) (lamb (inv we)) ∙
          ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ m ◻ inv we) (eta we) ∙
          ! (ap (λ m → f ◻ m) (α (inv we) f (inv we))) ∙
          α f (inv we) (⟦ ξB ⟧ f ◻ inv we) ∙
          ! (ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we) (eps we)) ∙
          ! (lamb (f ◻ inv we))) ◃∎ ∎ₛ

  wkeqv-bc-promote : {a b : B₀} → WkEquiv-bc ξB a b → AdjEquiv ξB a b
  fst (wkeqv-bc-promote (f , we)) = f
  inv (snd (wkeqv-bc-promote (f , we))) = inv we
  eta (snd (wkeqv-bc-promote (f , we))) = eta we
  eps (snd (wkeqv-bc-promote (f , we))) =
    eps we ∙
    ap (λ m → f ◻ m) (lamb (inv we)) ∙
    ap (λ m → f ◻ m ◻ inv we) (eta we) ∙
    ! (ap (λ m → f ◻ m) (α (inv we) f (inv we))) ∙
    α f (inv we) (f ◻ inv we) ∙
    ! (ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we) (eps we)) ∙
    ! (lamb (f ◻ inv we))
  coher-map (snd (wkeqv-bc-promote e)) = =ₛ-out $
    wkeqv-refine0 e ∙ₛ wkeqv-refine1 e ∙ₛ wkeqv-refine2 e ∙ₛ wkeqv-refine3 e ∙ₛ wkeqv-refine4 e ∙ₛ wkeqv-refine5 e
  coher-inv (snd (wkeqv-bc-promote (f , we))) = cohmap-to-cohinv
    (Wk-eqv (inv we) (eta we) (eps (snd (wkeqv-bc-promote (f , we)))))
    (coher-map (snd (wkeqv-bc-promote (f , we))))

  -- composition of equivalences

  infix 50 _WkEqv-bc-∘_
  _WkEqv-bc-∘_ : {a b c : B₀} → WkEquiv-bc ξB b c → WkEquiv-bc ξB a b → WkEquiv-bc ξB a c
  fst (g , aeg WkEqv-bc-∘ f , aef) = g ◻ f
  inv (snd (g , aeg WkEqv-bc-∘ f , aef)) = inv aef ◻ inv aeg
  eta (snd (g , aeg WkEqv-bc-∘ f , aef)) =
    eta aef ∙
    ap (λ m → m ◻ f) (ρ (inv aef)) ∙
    ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv aef ◻ m ◻ f) (eta aeg) ∙
    ap (λ m → m ◻ f) (α (inv aef) (inv aeg) g) ∙
    ! (α (inv aef ◻ inv aeg) g f) 
  eps (snd (g , aeg WkEqv-bc-∘ f , aef)) = 
    eps aeg ∙
    ap (λ m → g ◻ m) (lamb (inv aeg)) ∙
    ap (λ m → ⟦ ξB ⟧ g ◻ ⟦ ξB ⟧ m ◻ inv aeg) (eps aef) ∙
    ! (ap (λ m → g ◻ m) (α f (inv aef) (inv aeg))) ∙
    α g f (inv aef ◻ inv aeg)

  infix 50 _AdjEqv-∘_
  _AdjEqv-∘_ : {a b c : B₀} → AdjEquiv ξB b c → AdjEquiv ξB a b → AdjEquiv ξB a c
  g AdjEqv-∘ f = wkeqv-bc-promote (adjeqv-frg g WkEqv-bc-∘ adjeqv-frg f)
