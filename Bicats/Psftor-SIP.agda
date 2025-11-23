{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import lib.Equivalence2
open import lib.FTID
open import lib.types.Paths
open import lib.types.Sigma
open import lib.types.Pi
open import Bicategory
open import AdjEq
open import Pstransf
open import Pstransf-id
open import Univ-bc

-- SIP for (non-coherent) pseudofunctors

module Psftor-SIP where

open BicatStr {{...}}
open Psfunctor-nc
open PsfunctorNcStr
open Pstrans

module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂} {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}}
  {R₁ : Psfunctor-nc {{ξB}} {{ξC}}} (uC : is-univ-bc ξC) where

    private
      tot-sp =
        [ (M , Ar) ∈ Σ (Π B₀ (λ x → Σ C₀ (λ b → Σ (hom (map-pf R₁ x) b) Adjequiv)))
          (λ M → (((x , y) , f) : Σ (B₀ × B₀) (λ (x , y) → hom x y)) →
            Σ (hom (fst (M x)) (fst (M y))) (λ k →
                ⟦ ξC ⟧ k ◻ fst (snd (M x)) == ⟦ ξC ⟧ fst (snd (M y)) ◻ F₁ (str-pf R₁) f)) ] ×
          ((x : B₀) →
            Σ (fst (Ar ((x , x) , id₁ x)) == id₁ (fst (M x)))
              (λ R-id →
                lamb (fst (snd (M x))) ∙
                ap (λ m → ⟦ ξC ⟧ m ◻ fst (snd (M x))) (! R-id) ∙
                snd (Ar ((x , x) , id₁ x)) ∙
                ap (λ m → ⟦ ξC ⟧ fst (snd (M x)) ◻ m) (F-id₁ (str-pf R₁) x)
                  ==
                ρ (fst (snd (M x))))) ×
            ((((x , y , z) , f , g) : Σ (B₀ × B₀ × B₀) (λ (x , y , z) → hom x y × hom y z)) →
             Σ (fst (Ar ((x , z) , ⟦ ξB ⟧ g ◻ f)) == ⟦ ξC ⟧ fst (Ar ((y , z) , g)) ◻ fst (Ar ((x , y) , f)))
               (λ R-∘ →
                 ! (snd (Ar ((x , z) , ⟦ ξB ⟧ g ◻ f))) ∙
                 ap (λ m → ⟦ ξC ⟧ m ◻ fst (snd (M x))) R-∘ ∙
                 ! (α (fst (Ar ((y , z) , g))) (fst (Ar ((x , y) , f))) (fst (snd (M x)))) ∙
                 ap (λ m → ⟦ ξC ⟧ fst (Ar ((y , z) , g)) ◻ m) (snd (Ar ((x , y) , f))) ∙
                 α (fst (Ar ((y , z) , g))) (fst (snd (M y))) (F₁ (str-pf R₁) f) ∙
                 ap (λ m → ⟦ ξC ⟧ m ◻ (F₁ (str-pf R₁) f)) (snd (Ar ((y , z) , g))) ∙
                 ! (α (fst (snd (M z))) (F₁ (str-pf R₁) g) (F₁ (str-pf R₁) f)) ∙
                 ! (ap (λ m → ⟦ ξC ⟧ fst (snd (M z)) ◻ m) (F-◻ (str-pf R₁) f g))
                   ==
                 idp))
                 
    psftor-contr-aux2 : is-contr $
      Σ (Π B₀ (λ x → Σ C₀ (λ c → Σ (hom (map-pf R₁ x) c) Adjequiv)))
        (λ M → (((x , y) , f) : Σ (B₀ × B₀) (λ (x , y) → hom x y)) →
          Σ (hom (fst (M x)) (fst (M y))) (λ k →
            ⟦ ξC ⟧ k ◻ fst (snd (M x)) == ⟦ ξC ⟧ fst (snd (M y)) ◻ F₁ (str-pf R₁) f))
    psftor-contr-aux2 =
      equiv-preserves-level
        ((Σ-contr-red
          {A = Π B₀ (λ x → Σ C₀ (λ c → Σ (hom (map-pf R₁ x) c) Adjequiv))}
          (Π-level λ x → equiv-preserves-level (Σ-emap-r (λ c → is-univ-bc-≃ uC))))⁻¹)
          {{Π-level λ ((x , y) , f) →
            equiv-preserves-level
              (Σ-emap-r (λ k → pre∙'-equiv (! (ρ k))))}}

    psftor-contr-aux : is-contr tot-sp
    psftor-contr-aux = let cc = snd (contr-center psftor-contr-aux2) in
      equiv-preserves-level
        ((Σ-contr-red psftor-contr-aux2)⁻¹)
        {{×-level
          (Π-level (λ x → ∙-≃-∙2-contr {b = id₁ _} id₁-bc-rght-≃ (lamb (id₁ _)) (ap (λ m → ⟦ ξC ⟧ id₁ _ ◻ m) (F-id₁ (str-pf R₁) x))))
          (Π-level (λ ((x , y , z) , f , g) → 
            ∙-≃-∙6-contr {b = ⟦ ξC ⟧ fst (cc (_ , g)) ◻ fst (cc (_ , f))} id₁-bc-rght-≃ (! (α _ _ (id₁ _))) (α _ (id₁ _) (F₁ (str-pf R₁) f))
               (! (α (id₁ _) (F₁ (str-pf R₁) g) (F₁ (str-pf R₁) f))) (! (ap (λ m → ⟦ ξC ⟧ id₁ _ ◻ m) (F-◻ (str-pf R₁) f g)))))}}

{-
    abstract
      psftor-contr : is-contr (Σ (Psfunctor-nc {{ξB}} {{ξC}}) (λ R₂ → R₁ ps-≃ R₂))
      psftor-contr = equiv-preserves-level lemma {{psftor-contr-aux}}
        where
          lemma : tot-sp ≃ Σ (Psfunctor-nc {{ξB}} {{ξC}}) (λ R₂ → R₁ ps-≃ R₂)
          lemma = 
            equiv
              (λ ((M , Ar) , R-id , R-∘) →
                (functor-wc (fst ∘ M) (λ f → fst (Ar (_ , f))) (fst ∘ R-id) λ f g → fst (F-∘ (_ , f , g))) ,
                ((pstrans (λ x → fst (snd (M x))) (λ f → snd (Ar (_ , f))) (snd ∘ R-id) λ f g → snd (F-∘ (_ , f , g))) ,
                  λ x → snd (snd (M x))))
              (λ ((functor-wc M₁ Ar₁ R-id₁ R-∘₁) , (pstrans M₁₂ Ar₂ R-id₂ R-∘₂ , M₂₂)) →
                ((λ x → (M₁ x) , ((M₁₂ x) , (M₂₂ x))) , (λ (_ , f) → (Ar₁ f) , (Ar₂ f))) ,
                (λ x → (F-id₁ x) , (F-id₂ x)) , (λ (_ , f , g) → (F-∘₁ f g) , (F-∘₂ f g)))
              (λ _ → idp)
              λ _ → idp

    psftor-ind : ∀ {k} (Q : (F₂ : Psfunctor-nc {{ξB}} {{ξC}}) → (R₁ ps-≃ R₂ → Type k))
      → Q R₁ ps-≃-id → {F₂ : Psfunctor-nc {{ξB}} {{ξC}}} (e : R₁ ps-≃ R₂) → Q R₂ e
    psftor-ind Q = ID-ind-map Q psftor-contr

    psftor-ind-β : ∀ {k} (Q : (F₂ : Psfunctor-nc {{ξB}} {{ξC}}) → (R₁ ps-≃ R₂ → Type k))
      → (r : Q R₁ ps-≃-id) → psftor-ind Q r ps-≃-id == r
    psftor-ind-β Q = ID-ind-map-β Q psftor-contr
-}
