{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import lib.Basics
open import lib.Equivalence2
open import lib.NType2
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
        [ (M , Ar) ∈ Σ (Π B₀ (λ x → Σ C₀ (λ b → Σ (hom (map-pf R₁ x) b) (Adjequiv {{ξC}}))))
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
    psftor-contr-aux =
      let
        cc₁ x = fst (fst (contr-center psftor-contr-aux2) x)
        cc₂ = snd (contr-center psftor-contr-aux2)
      in
      equiv-preserves-level
        ((Σ-contr-red psftor-contr-aux2)⁻¹)
        {{×-level
          (Π-level (λ x →
            ∙-≃-∙2-contr {b = id₁ (cc₁ x)} id₁-bc-rght-≃
              (lamb (id₁ (cc₁ x)))
              (ap (λ m → ⟦ ξC ⟧ id₁ (fst (fst (contr-center psftor-contr-aux2) x)) ◻ m) (F-id₁ (str-pf R₁) x))))
          (Π-level (λ ((x , y , z) , f , g) → 
            ∙-≃-∙6-contr {b = ⟦ ξC ⟧ fst (cc₂ (_ , g)) ◻ fst (cc₂ (_ , f))} id₁-bc-rght-≃
              {p₀ = ! (snd (cc₂ (_ ,  ⟦ ξB ⟧ g ◻ f)))}
              (! (α _ _ (id₁ (cc₁ x))))
              {p₂ = ap (λ m → ⟦ ξC ⟧ fst (cc₂ (_ ,  g)) ◻ m) (snd (cc₂ (_ ,  f)))}
              (α _ (id₁ (cc₁ y)) (F₁ (str-pf R₁) f))
              {p₄ = ap (λ m → ⟦ ξC ⟧ m ◻ (F₁ (str-pf R₁) f)) (snd (cc₂ (_ ,  g)))}
              (! (α (id₁ (cc₁ z)) (F₁ (str-pf R₁) g) (F₁ (str-pf R₁) f)))
              (! (ap (λ m → ⟦ ξC ⟧ id₁ (cc₁ z) ◻ m) (F-◻ (str-pf R₁) f g)))))}}

    abstract
      psftor-contr : is-contr (Σ (Psfunctor-nc {{ξB}} {{ξC}}) (λ R₂ → R₁ ps-≃ R₂))
      psftor-contr = equiv-preserves-level lemma {{psftor-contr-aux}}
        where
          lemma : tot-sp ≃ Σ (Psfunctor-nc {{ξB}} {{ξC}}) (λ R₂ → R₁ ps-≃ R₂)
          lemma = 
            equiv
              (λ ((M , Ar) , R-ids , R-∘s) → psfunctornc {{ξB}} {{ξC}} (fst ∘ M)
                {{psfunctorncstr (λ f → fst (Ar (_ , f))) (fst ∘ R-ids) λ f g → fst (R-∘s (_ , f , g))}} ,
                (pstrans (fst ∘ snd ∘ M) (λ f → snd (Ar (_ , f))) (λ {a} → snd (R-ids a))
                λ f g → snd (R-∘s (_ , f , g))) , λ x → (snd (snd (M x))))
              (λ (psfunctornc M {{psfunctorncstr Ar R-id R-∘}} , (pstrans cs sqs cu ca , es)) →
                ((λ x → (M x) , ((cs x) , (es x))) ,
                  (λ (_ , f) → (Ar f) , (sqs f))) , ((λ x → (R-id x) , cu {x}) , (λ (_ , f , g) → R-∘ f g , ca f g)))
              (λ _ → idp)
              λ _ → idp

    psftor-ind : ∀ {k} (Q : (R₂ : Psfunctor-nc {{ξB}} {{ξC}}) → (R₁ ps-≃ R₂ → Type k))
      → Q R₁ ps-≃-id → {R₂ : Psfunctor-nc {{ξB}} {{ξC}}} (e : R₁ ps-≃ R₂) → Q R₂ e
    psftor-ind Q = ID-ind-map Q psftor-contr
    
    psftor-ind-β : ∀ {k} (Q : (R₂ : Psfunctor-nc {{ξB}} {{ξC}}) → (R₁ ps-≃ R₂ → Type k))
      → (r : Q R₁ ps-≃-id) → psftor-ind Q r ps-≃-id == r
    psftor-ind-β Q = ID-ind-map-β Q psftor-contr

    ps-≃-to-== : {R₂ : Psfunctor-nc {{ξB}} {{ξC}}} → R₁ ps-≃ R₂ → R₁ == R₂
    ps-≃-to-== {R₂} = psftor-ind (λ R₂ _ → R₁ == R₂) idp

    ps-≃-to-==-β : ps-≃-to-== ps-≃-id == idp
    ps-≃-to-==-β = psftor-ind-β (λ R₂ _ → R₁ == R₂) idp

    ps-≃-from-== : {R₂ : Psfunctor-nc {{ξB}} {{ξC}}} → R₁ == R₂ → R₁ ps-≃ R₂
    ps-≃-from-== idp = ps-≃-id

    ps-≃-==-≃ : {R₂ : Psfunctor-nc {{ξB}} {{ξC}}} → (R₁ == R₂) ≃ (R₁ ps-≃ R₂)
    ps-≃-==-≃ = equiv ps-≃-from-== ps-≃-to-== aux1 aux2
      where

        aux1 : ∀ {R₂} (p : R₁ ps-≃ R₂) → ps-≃-from-== (ps-≃-to-== p) == p
        aux1 = psftor-ind (λ _ p → ps-≃-from-== (ps-≃-to-== p) == p) (ap ps-≃-from-== ps-≃-to-==-β)

        aux2 : ∀ {R₂} (p : R₁ == R₂) → ps-≃-to-== (ps-≃-from-== p) == p
        aux2 idp = ps-≃-to-==-β

module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂} {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}} (uC : is-univ-bc ξC) where

  psf-≃-==-≃ : {R₁ R₂ : Psfunctor {{ξB}} {{ξC}}} → (R₁ == R₂) ≃ (psftor-str R₁ ps-≃ psftor-str R₂)
  psf-≃-==-≃ =
    ps-≃-==-≃ uC ∘e
    (Subtype=-econv (subtypeprop Psf-coh-data {{λ {ψ} → Psf-coh-data-is-prop {ψ = ψ}}}) _ _)⁻¹ ∘e
    ap-equiv Psftor-Σ-≃  _ _

  psf-≃-to-== : {R₁ R₂ : Psfunctor {{ξB}} {{ξC}}} → psftor-str R₁ ps-≃ psftor-str R₂ → R₁ == R₂
  psf-≃-to-== = <– psf-≃-==-≃

  Psf-coh-induce : (R₁ : Psfunctor {{ξB}} {{ξC}}) {R₂ : Psfunctor-nc {{ξB}} {{ξC}}}
    → psftor-str R₁ ps-≃ R₂ → Psf-coh-data R₂
  Psf-coh-induce R₁ = psftor-ind uC (λ R₂ _ → Psf-coh-data R₂) (F-ρ (str-pf R₁) , (F-λ (str-pf R₁) , F-α (str-pf R₁)))
    where
      open Psfunctor
      open PsfunctorStr
