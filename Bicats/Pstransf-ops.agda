{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Pi
open import Bicategory
open import Pstransf
open import AdjEq
open import Psftor-SIP
open import Pstransf-id
open import Pstransf-SIP
open import Univ-bc
open import Bicat-coher

-- operations on pseudotransformations

module Pstransf-ops where

open BicatStr {{...}}
open Psfunctor
open PsfunctorStr
open Psfunctor-nc
open PsfunctorNcStr
open Pstrans-nc

module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂} {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}} where

  -- composition
  
  infixr 10 _pstrans-∙_
  _pstrans-∙_ : {R₁ R₂ R₃ : Psfunctor-nc {{ξB}} {{ξC}}} → Pstrans-nc R₁ R₂ → Pstrans-nc R₂ R₃ → Pstrans-nc R₁ R₃
  η₀ (T₁ pstrans-∙ T₂) a = ⟦ ξC ⟧ η₀ T₂ a ◻ η₀ T₁ a
  η₁ (_pstrans-∙_ {R₁} {R₂} {R₃} T₁ T₂) {x} {y} f = 
    -- ⟦ ξC ⟧ F₁ (str-pf R₃) f ◻ ⟦ ξC ⟧ η₀ T₂ x ◻ η₀ T₁ x
    α (F₁ (str-pf R₃) f) (η₀ T₂ x) (η₀ T₁ x) ∙
    -- ⟦ ξC ⟧ (⟦ ξC ⟧ F₁ (str-pf R₃) f ◻  η₀ T₂ x) ◻ η₀ T₁ x
    ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ x) (η₁ T₂ f) ∙
    -- ⟦ ξC ⟧ (⟦ ξC ⟧ η₀ T₂ y ◻ F₁ (str-pf R₂) f) ◻ η₀ T₁ x
    ! (α (η₀ T₂ y) (F₁ (str-pf R₂) f) (η₀ T₁ x)) ∙
    -- ⟦ ξC ⟧ η₀ T₂ y ◻ ⟦ ξC ⟧ F₁ (str-pf R₂) f ◻ η₀ T₁ x
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ y ◻ m) (η₁ T₁ f) ∙
    -- ⟦ ξC ⟧ η₀ T₂ y ◻ ⟦ ξC ⟧ η₀ T₁ y ◻ F₁ (str-pf R₁) f
    α (η₀ T₂ y) (η₀ T₁ y) (F₁ (str-pf R₁) f)
    -- ⟦ ξC ⟧ (⟦ ξC ⟧ η₀ T₂ y ◻ η₀ T₁ y) ◻ F₁ (str-pf R₁) f

  ps-≃-∙ : is-univ-bc ξC → {R₁ R₂ : Psfunctor-nc {{ξB}} {{ξC}}} →
    R₁ psf-≃ R₂ → ((R₃ , _) : Σ (Psfunctor-nc {{ξB}} {{ξC}}) (λ R₃ → R₂ psf-≃ R₃)) → R₁ psf-≃ R₃
  ps-≃-∙ uC {R₁} pe p = psftor-ind uC (λ R₂ pe → ∀ p → R₁ psf-≃ fst p) snd pe p

  -- whiskering
  module _ {i₃ j₃} {D₀ : Type i₃} {{ξD : BicatStr j₃ D₀}} {R₁ : Psfunctor-nc {{ξB}} {{ξC}}} where

    pstrans-whisk-l : {R₂ : Psfunctor-nc {{ξB}} {{ξC}}} →
      Pstrans-nc R₁ R₂ → (G : Psfunctor-nc {{ξC}} {{ξD}}) → Pstrans-nc (G ∘BC-s R₁) (G ∘BC-s R₂)
    η₀ (pstrans-whisk-l τ G) x = F₁ (str-pf G) (η₀ τ x)
    η₁ (pstrans-whisk-l {R₂} τ G) {x} {y} f = 
      -- ⟦ ξC ⟧ F₁ (str-pf G) (F₁ (str-pf R₂) f) ◻ F₁ (str-pf G) (η₀ τ x)
      ! (F-◻ (str-pf G) (η₀ τ x) (F₁ (str-pf R₂) f)) ∙
      -- F₁ (str-pf G) (⟦ ξB ⟧ F₁ (str-pf R₂) f ◻ η₀ τ x)
      ap (F₁ (str-pf G)) (η₁ τ f) ∙
      -- F₁ (str-pf G) (⟦ ξB ⟧ η₀ τ y ◻ F₁ (str-pf R₁) f)
      F-◻ (str-pf G) (F₁ (str-pf R₁) f) (η₀ τ y)
      -- ⟦ ξC ⟧ F₁ (str-pf G) (η₀ τ y) ◻ F₁ (str-pf G) (F₁ (str-pf R₁) f)

    pstrans-whisk-r : {R₂ : Psfunctor-nc {{ξB}} {{ξC}}} →
      Pstrans-nc R₁ R₂ → (G : Psfunctor-nc {{ξD}} {{ξB}}) → Pstrans-nc (R₁ ∘BC-s G) (R₂ ∘BC-s G)
    η₀ (pstrans-whisk-r τ G) x = η₀ τ (map-pf G x)
    η₁ (pstrans-whisk-r τ G) f = η₁ τ (F₁ (str-pf G) f)

    ps-≃-whisk-l : is-univ-bc ξC → {R₂ : Psfunctor-nc {{ξB}} {{ξC}}} →
      R₁ psf-≃ R₂ → (G : Psfunctor-nc {{ξC}} {{ξD}}) → (G ∘BC-s R₁) psf-≃ (G ∘BC-s R₂)
    ps-≃-whisk-l uC = psftor-ind uC (λ R₂ pe → ∀ G → (G ∘BC-s R₁) psf-≃ (G ∘BC-s R₂)) λ _ → ps-≃-id

    ps-≃-whisk-r : is-univ-bc ξC → {R₂ : Psfunctor-nc {{ξB}} {{ξC}}} →
      R₁ psf-≃ R₂ → (G : Psfunctor-nc {{ξD}} {{ξB}}) → (R₁ ∘BC-s G) psf-≃ (R₂ ∘BC-s G)
    ps-≃-whisk-r uC = psftor-ind uC (λ R₂ pe → ∀ G → (R₁ ∘BC-s G) psf-≃ (R₂ ∘BC-s G)) λ _ → ps-≃-id

  -- induced coherence data on the above operations via univalence
  module _ (uC : is-univ-bc ξC) where

    open Pstrans

    pstrans-∙-coh-data : {R₁ R₂ : Psfunctor-nc {{ξB}} {{ξC}}} (T₁ : R₁ psf-≃ R₂) {R₃ : Psfunctor-nc {{ξB}} {{ξC}}}
      (T₂ : R₂ psf-≃ R₃) → Pst-coh-data (pstrans-str (fst T₁) pstrans-∙ pstrans-str (fst T₂))
    pstrans-∙-coh-data {R₁} = psftor-ind uC
      (λ R₂ T₁ → ∀ {R₃} T₂ → Pst-coh-data (pstrans-str (fst T₁) pstrans-∙ pstrans-str (fst T₂)))
      λ {R₃} T₂ →
        Pstrans-coh-induce (fst (ps-≃-∙ uC ps-≃-id (R₃ , T₂))) {pstrans-str Pstrans-id pstrans-∙ pstrans-str (fst T₂)}
        (pst-≃ (λ x → aux-comp T₂ x) (λ {a b} f →  η₁-∼-flip (aux-sq T₂ f)))
      module pstrans-∙-cd where
      
        aux-comp : {R₃ : Psfunctor-nc {{ξB}} {{ξC}}} (T₂ : R₁ psf-≃ R₃) (x : B₀)
          → η₀ (fst (ps-≃-∙ uC ps-≃-id (R₃ , T₂))) x == ⟦ ξC ⟧ η₀ (fst T₂) x ◻ id₁ (map-pf R₁ x)
        aux-comp {R₃} T₂ x =
          ap (λ t → η₀ t x) (ap fst (app= (psftor-ind-β uC (λ R₂ pe → ∀ p → R₁ psf-≃ fst p) snd) (R₃ , T₂))) ∙
          ρ (η₀ (fst T₂) x)
          
        abstract
          aux-sq : {R₃ : Psfunctor-nc {{ξB}} {{ξC}}} (T₂ : R₁ psf-≃ R₃) {a b : B₀} (f : hom a b) →
            ! (η₁ (fst (ps-≃-∙ uC ps-≃-id (R₃ , T₂))) f) ◃∙
            ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R₃) f ◻ m)
              (ap (λ t → η₀ t a)
                (ap fst (app=
                  (psftor-ind-β uC (λ R₂ pe → ∀ p →
                    R₁ psf-≃ fst p) snd) (R₃ , T₂))) ∙
                ρ (η₀ (fst T₂) a)) ◃∙
             (α (F₁ (str-pf R₃) f) (η₀ (fst T₂) a) (id₁ (map-pf R₁ a)) ∙
             ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R₁ a)) (η₁ (fst T₂) f) ∙
             ! (α (η₀ (fst T₂) b) (F₁ (str-pf R₁) f) (id₁ (map-pf R₁ a))) ∙
             ap (λ m → ⟦ ξC ⟧ η₀ (fst T₂) b ◻ m) (! (ρ (F₁ (str-pf R₁) f)) ∙ lamb (F₁ (str-pf R₁) f)) ∙
             α (η₀ (fst T₂) b) (id₁ (map-pf R₁ b)) (F₁ (str-pf R₁) f)) ◃∙
             ! (ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R₁) f)
                 (ap (λ t → η₀ t b)
                   (ap fst (app=
                     (psftor-ind-β uC (λ R₂ pe → ∀ p →
                       R₁ psf-≃ fst p) snd) (R₃ , T₂))) ∙
                   ρ (η₀ (fst T₂) b))) ◃∎
               =ₛ
             idp ◃∎
          aux-sq {R₃} T₂ {a} {b} f = 
            ! (η₁ (fst (ps-≃-∙ uC ps-≃-id (R₃ , T₂))) f) ◃∙
            ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R₃) f ◻ m)
              (ap (λ t → η₀ t a)
                (ap fst (app=
                  (psftor-ind-β uC (λ R₂ pe → ∀ p →
                    R₁ psf-≃ fst p) snd) (R₃ , T₂))) ∙
                ρ (η₀ (fst T₂) a)) ◃∙
            (α (F₁ (str-pf R₃) f) (η₀ (fst T₂) a) (id₁ (map-pf R₁ a)) ∙
            ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R₁ a)) (η₁ (fst T₂) f) ∙
            ! (α (η₀ (fst T₂) b) (F₁ (str-pf R₁) f) (id₁ (map-pf R₁ a))) ∙
            ap (λ m → ⟦ ξC ⟧ η₀ (fst T₂) b ◻ m) (! (ρ (F₁ (str-pf R₁) f)) ∙ lamb (F₁ (str-pf R₁) f)) ∙
            α (η₀ (fst T₂) b) (id₁ (map-pf R₁ b)) (F₁ (str-pf R₁) f)) ◃∙
            ! (ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R₁) f)
                (ap (λ t → η₀ t b)
                  (ap fst (app=
                    (psftor-ind-β uC (λ R₂ pe → ∀ p →
                      R₁ psf-≃ fst p) snd) (R₃ , T₂))) ∙
                  ρ (η₀ (fst T₂) b))) ◃∎
              =ₛ⟨ 3 & 1 & !-ap-∘-∙◃ (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R₁) f) (λ t → η₀ t b)
                (ap fst (app=
                  (psftor-ind-β uC (λ R₂ pe → ∀ p →
                    R₁ psf-≃ fst p) snd) (R₃ , T₂)))
                (ρ (η₀ (fst T₂) b)) ⟩
            ! (η₁ (fst (ps-≃-∙ uC ps-≃-id (R₃ , T₂))) f) ◃∙
            ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R₃) f ◻ m)
              (ap (λ t → η₀ t a)
                (ap fst (app=
                  (psftor-ind-β uC (λ R₂ pe → ∀ p →
                    R₁ psf-≃ fst p) snd) (R₃ , T₂))) ∙
                ρ (η₀ (fst T₂) a)) ◃∙
            (α (F₁ (str-pf R₃) f) (η₀ (fst T₂) a) (id₁ (map-pf R₁ a)) ∙
            ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R₁ a)) (η₁ (fst T₂) f) ∙
            ! (α (η₀ (fst T₂) b) (F₁ (str-pf R₁) f) (id₁ (map-pf R₁ a))) ∙
            ap (λ m → ⟦ ξC ⟧ η₀ (fst T₂) b ◻ m) (! (ρ (F₁ (str-pf R₁) f)) ∙ lamb (F₁ (str-pf R₁) f)) ∙
            α (η₀ (fst T₂) b) (id₁ (map-pf R₁ b)) (F₁ (str-pf R₁) f)) ◃∙
            ! (ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R₁) f) (ρ (η₀ (fst T₂) b))) ◃∙
            ! (ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ F₁ (str-pf R₁) f)
                (ap fst (app=
                  (psftor-ind-β uC (λ R₂ pe → ∀ p →
                    R₁ psf-≃ fst p) snd) (R₃ , T₂)))) ◃∎
              =ₑ⟨ 2 & 1 & 
                α (F₁ (str-pf R₃) f) (η₀ (fst T₂) a) (id₁ (map-pf R₁ a)) ◃∙
                ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R₁ a)) (η₁ (fst T₂) f) ◃∙
                ! (α (η₀ (fst T₂) b) (F₁ (str-pf R₁) f) (id₁ (map-pf R₁ a))) ◃∙
                ap (λ m → ⟦ ξC ⟧ η₀ (fst T₂) b ◻ m) (! (ρ (F₁ (str-pf R₁) f)) ∙ lamb (F₁ (str-pf R₁) f)) ◃∙
                α (η₀ (fst T₂) b) (id₁ (map-pf R₁ b)) (F₁ (str-pf R₁) f) ◃∎
                % =ₛ-in (idp {a =
                    (α (F₁ (str-pf R₃) f) (η₀ (fst T₂) a) (id₁ (map-pf R₁ a)) ∙
                    ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R₁ a)) (η₁ (fst T₂) f) ∙
                    ! (α (η₀ (fst T₂) b) (F₁ (str-pf R₁) f) (id₁ (map-pf R₁ a))) ∙
                    ap (λ m → ⟦ ξC ⟧ η₀ (fst T₂) b ◻ m) (! (ρ (F₁ (str-pf R₁) f)) ∙ lamb (F₁ (str-pf R₁) f)) ∙
                    α (η₀ (fst T₂) b) (id₁ (map-pf R₁ b)) (F₁ (str-pf R₁) f))}) ⟩
            ! (η₁ (fst (ps-≃-∙ uC ps-≃-id (R₃ , T₂))) f) ◃∙
            ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R₃) f ◻ m)
              (ap (λ t → η₀ t a)
                (ap fst (app=
                  (psftor-ind-β uC (λ R₂ pe → ∀ p →
                    R₁ psf-≃ fst p) snd) (R₃ , T₂))) ∙
                ρ (η₀ (fst T₂) a)) ◃∙
            α (F₁ (str-pf R₃) f) (η₀ (fst T₂) a) (id₁ (map-pf R₁ a)) ◃∙
            ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R₁ a)) (η₁ (fst T₂) f) ◃∙
            ! (α (η₀ (fst T₂) b) (F₁ (str-pf R₁) f) (id₁ (map-pf R₁ a))) ◃∙
            ap (λ m → ⟦ ξC ⟧ η₀ (fst T₂) b ◻ m) (! (ρ (F₁ (str-pf R₁) f)) ∙ lamb (F₁ (str-pf R₁) f)) ◃∙
            α (η₀ (fst T₂) b) (id₁ (map-pf R₁ b)) (F₁ (str-pf R₁) f) ◃∙
            ! (ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R₁) f) (ρ (η₀ (fst T₂) b))) ◃∙
            ! (ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ F₁ (str-pf R₁) f)
                (ap fst (app=
                  (psftor-ind-β uC (λ R₂ pe → ∀ p →
                    R₁ psf-≃ fst p) snd) (R₃ , T₂)))) ◃∎
              =ₛ⟨ 1 & 1 & ap-∘-∙◃ (λ m → ⟦ ξC ⟧ F₁ (str-pf R₃) f ◻ m) (λ t → η₀ t a)
                (ap fst (app=
                  (psftor-ind-β uC (λ R₂ pe → ∀ p →
                    R₁ psf-≃ fst p) snd) (R₃ , T₂)))
                (ρ (η₀ (fst T₂) a)) ⟩
            ! (η₁ (fst (ps-≃-∙ uC ps-≃-id (R₃ , T₂))) f) ◃∙
            ap (λ t → ⟦ ξC ⟧ F₁ (str-pf R₃) f ◻ η₀ t a)
              (ap fst (app=
                (psftor-ind-β uC (λ R₂ pe → ∀ p →
                  R₁ psf-≃ fst p) snd) (R₃ , T₂))) ◃∙
            ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R₃) f ◻ m) (ρ (η₀ (fst T₂) a)) ◃∙
            α (F₁ (str-pf R₃) f) (η₀ (fst T₂) a) (id₁ (map-pf R₁ a)) ◃∙
            ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R₁ a)) (η₁ (fst T₂) f) ◃∙
            ! (α (η₀ (fst T₂) b) (F₁ (str-pf R₁) f) (id₁ (map-pf R₁ a))) ◃∙
            ap (λ m → ⟦ ξC ⟧ η₀ (fst T₂) b ◻ m) (! (ρ (F₁ (str-pf R₁) f)) ∙ lamb (F₁ (str-pf R₁) f)) ◃∙
            α (η₀ (fst T₂) b) (id₁ (map-pf R₁ b)) (F₁ (str-pf R₁) f) ◃∙
            ! (ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R₁) f) (ρ (η₀ (fst T₂) b))) ◃∙
            ! (ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ F₁ (str-pf R₁) f)
                (ap fst (app=
                  (psftor-ind-β uC (λ R₂ pe → ∀ p →
                    R₁ psf-≃ fst p) snd) (R₃ , T₂)))) ◃∎
              =ₛ⟨ 0 & 1 & hmtpy-nat-!◃ (λ t → Pstrans.η₁ t f)
                (ap fst (app= (psftor-ind-β uC (λ R₂ pe → ∀ p → R₁ psf-≃ fst p) snd) (R₃ , T₂))) ⟩
            ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ F₁ (str-pf R₁) f)
              (ap fst (app= (psftor-ind-β uC (λ R₂ pe → ∀ p → R₁ psf-≃ fst p) snd) (R₃ , T₂))) ◃∙
            ! (η₁ (fst T₂) f) ◃∙
            ! (ap (λ t → ⟦ ξC ⟧ F₁ (str-pf R₃) f ◻ η₀ t a)
                (ap fst (app= (psftor-ind-β uC (λ R₂ pe → ∀ p → R₁ psf-≃ fst p) snd) (R₃ , T₂)))) ◃∙
            ap (λ t → ⟦ ξC ⟧ F₁ (str-pf R₃) f ◻ η₀ t a)
              (ap fst (app= (psftor-ind-β uC (λ R₂ pe → ∀ p → R₁ psf-≃ fst p) snd) (R₃ , T₂))) ◃∙
            ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R₃) f ◻ m) (ρ (η₀ (fst T₂) a)) ◃∙
            α (F₁ (str-pf R₃) f) (η₀ (fst T₂) a) (id₁ (map-pf R₁ a)) ◃∙
            ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R₁ a)) (η₁ (fst T₂) f) ◃∙
            ! (α (η₀ (fst T₂) b) (F₁ (str-pf R₁) f) (id₁ (map-pf R₁ a))) ◃∙
            ap (λ m → ⟦ ξC ⟧ η₀ (fst T₂) b ◻ m) (! (ρ (F₁ (str-pf R₁) f)) ∙ lamb (F₁ (str-pf R₁) f)) ◃∙
            α (η₀ (fst T₂) b) (id₁ (map-pf R₁ b)) (F₁ (str-pf R₁) f) ◃∙
            ! (ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R₁) f) (ρ (η₀ (fst T₂) b))) ◃∙
            ! (ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ F₁ (str-pf R₁) f)
                (ap fst (app=
                  (psftor-ind-β uC (λ R₂ pe → ∀ p →
                    R₁ psf-≃ fst p) snd) (R₃ , T₂)))) ◃∎
              =ₛ⟨ 2 & 2 & !-inv-l◃ (ap (λ t → ⟦ ξC ⟧ F₁ (str-pf R₃) f ◻ η₀ t a)
                (ap fst (app= (psftor-ind-β uC (λ R₂ pe → ∀ p → R₁ psf-≃ fst p) snd) (R₃ , T₂)))) ⟩
            ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ F₁ (str-pf R₁) f)
              (ap fst (app= (psftor-ind-β uC (λ R₂ pe → ∀ p → R₁ psf-≃ fst p) snd) (R₃ , T₂))) ◃∙
            ! (η₁ (fst T₂) f) ◃∙
            ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R₃) f ◻ m) (ρ (η₀ (fst T₂) a)) ◃∙
            α (F₁ (str-pf R₃) f) (η₀ (fst T₂) a) (id₁ (map-pf R₁ a)) ◃∙
            ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R₁ a)) (η₁ (fst T₂) f) ◃∙
            ! (α (η₀ (fst T₂) b) (F₁ (str-pf R₁) f) (id₁ (map-pf R₁ a))) ◃∙
            ap (λ m → ⟦ ξC ⟧ η₀ (fst T₂) b ◻ m) (! (ρ (F₁ (str-pf R₁) f)) ∙ lamb (F₁ (str-pf R₁) f)) ◃∙
            α (η₀ (fst T₂) b) (id₁ (map-pf R₁ b)) (F₁ (str-pf R₁) f) ◃∙
            ! (ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R₁) f) (ρ (η₀ (fst T₂) b))) ◃∙
            ! (ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ F₁ (str-pf R₁) f)
                (ap fst (app=
                  (psftor-ind-β uC (λ R₂ pe → ∀ p →
                    R₁ psf-≃ fst p) snd) (R₃ , T₂)))) ◃∎
              =ₛ⟨ 2 & 2 & trig-ρ-bc (F₁ (str-pf R₃) f) (η₀ (fst T₂) a) ⟩
            ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ F₁ (str-pf R₁) f)
              (ap fst (app= (psftor-ind-β uC (λ R₂ pe → ∀ p → R₁ psf-≃ fst p) snd) (R₃ , T₂))) ◃∙
            ! (η₁ (fst T₂) f) ◃∙
            ρ (⟦ ξC ⟧ F₁ (str-pf R₃) f ◻ η₀ (fst T₂) a) ◃∙
            ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R₁ a)) (η₁ (fst T₂) f) ◃∙
            ! (α (η₀ (fst T₂) b) (F₁ (str-pf R₁) f) (id₁ (map-pf R₁ a))) ◃∙
            ap (λ m → ⟦ ξC ⟧ η₀ (fst T₂) b ◻ m) (! (ρ (F₁ (str-pf R₁) f)) ∙ lamb (F₁ (str-pf R₁) f)) ◃∙
            α (η₀ (fst T₂) b) (id₁ (map-pf R₁ b)) (F₁ (str-pf R₁) f) ◃∙
            ! (ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R₁) f) (ρ (η₀ (fst T₂) b))) ◃∙
            ! (ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ F₁ (str-pf R₁) f)
                (ap fst (app=
                  (psftor-ind-β uC (λ R₂ pe → ∀ p →
                    R₁ psf-≃ fst p) snd) (R₃ , T₂)))) ◃∎
              =ₛ⟨ 2 & 2 & !ₛ (homotopy-naturality _ _ ρ (η₁ (fst T₂) f)) ⟩
            ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ F₁ (str-pf R₁) f)
              (ap fst (app= (psftor-ind-β uC (λ R₂ pe → ∀ p → R₁ psf-≃ fst p) snd) (R₃ , T₂))) ◃∙
            ! (η₁ (fst T₂) f) ◃∙
            ap (λ m → m) (η₁ (fst T₂) f) ◃∙
            ρ (⟦ ξC ⟧ η₀ (fst T₂) b ◻ F₁ (str-pf R₁) f) ◃∙
            ! (α (η₀ (fst T₂) b) (F₁ (str-pf R₁) f) (id₁ (map-pf R₁ a))) ◃∙
            ap (λ m → ⟦ ξC ⟧ η₀ (fst T₂) b ◻ m) (! (ρ (F₁ (str-pf R₁) f)) ∙ lamb (F₁ (str-pf R₁) f)) ◃∙
            α (η₀ (fst T₂) b) (id₁ (map-pf R₁ b)) (F₁ (str-pf R₁) f) ◃∙
            ! (ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R₁) f) (ρ (η₀ (fst T₂) b))) ◃∙
            ! (ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ F₁ (str-pf R₁) f)
                (ap fst (app=
                  (psftor-ind-β uC (λ R₂ pe → ∀ p →
                    R₁ psf-≃ fst p) snd) (R₃ , T₂)))) ◃∎
              =ₛ⟨ 1 & 2 & ap-idf-!-l (η₁ (fst T₂) f) ⟩
            ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ F₁ (str-pf R₁) f)
              (ap fst (app= (psftor-ind-β uC (λ R₂ pe → ∀ p → R₁ psf-≃ fst p) snd) (R₃ , T₂))) ◃∙
            ρ (⟦ ξC ⟧ η₀ (fst T₂) b ◻ F₁ (str-pf R₁) f) ◃∙
            ! (α (η₀ (fst T₂) b) (F₁ (str-pf R₁) f) (id₁ (map-pf R₁ a))) ◃∙
            ap (λ m → ⟦ ξC ⟧ η₀ (fst T₂) b ◻ m) (! (ρ (F₁ (str-pf R₁) f)) ∙ lamb (F₁ (str-pf R₁) f)) ◃∙
            α (η₀ (fst T₂) b) (id₁ (map-pf R₁ b)) (F₁ (str-pf R₁) f) ◃∙
            ! (ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R₁) f) (ρ (η₀ (fst T₂) b))) ◃∙
            ! (ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ F₁ (str-pf R₁) f)
                (ap fst (app= (psftor-ind-β uC (λ R₂ pe → ∀ p → R₁ psf-≃ fst p) snd) (R₃ , T₂)))) ◃∎
              =ₛ⟨ 3 & 1 & ap-!∙◃ (λ m → ⟦ ξC ⟧ η₀ (fst T₂) b ◻ m) (ρ (F₁ (str-pf R₁) f)) (lamb (F₁ (str-pf R₁) f)) ⟩
            ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ F₁ (str-pf R₁) f)
              (ap fst (app= (psftor-ind-β uC (λ R₂ pe → ∀ p → R₁ psf-≃ fst p) snd) (R₃ , T₂))) ◃∙
            ρ (⟦ ξC ⟧ η₀ (fst T₂) b ◻ F₁ (str-pf R₁) f) ◃∙
            ! (α (η₀ (fst T₂) b) (F₁ (str-pf R₁) f) (id₁ (map-pf R₁ a))) ◃∙
            ! (ap (λ m → ⟦ ξC ⟧ η₀ (fst T₂) b ◻ m) (ρ (F₁ (str-pf R₁) f))) ◃∙
            ap (λ m → ⟦ ξC ⟧ η₀ (fst T₂) b ◻ m) (lamb (F₁ (str-pf R₁) f)) ◃∙
            α (η₀ (fst T₂) b) (id₁ (map-pf R₁ b)) (F₁ (str-pf R₁) f) ◃∙
            ! (ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R₁) f) (ρ (η₀ (fst T₂) b))) ◃∙
            ! (ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ F₁ (str-pf R₁) f)
                (ap fst (app= (psftor-ind-β uC (λ R₂ pe → ∀ p → R₁ psf-≃ fst p) snd) (R₃ , T₂)))) ◃∎
              =ₛ⟨ 1 & 3 & trig-ρ-bc-rot-pre (η₀ (fst T₂) b) (F₁ (str-pf R₁) f) ⟩
            ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ F₁ (str-pf R₁) f)
              (ap fst (app= (psftor-ind-β uC (λ R₂ pe → ∀ p → R₁ psf-≃ fst p) snd) (R₃ , T₂))) ◃∙
            ap (λ m → ⟦ ξC ⟧ η₀ (fst T₂) b ◻ m) (lamb (F₁ (str-pf R₁) f)) ◃∙
            α (η₀ (fst T₂) b) (id₁ (map-pf R₁ b)) (F₁ (str-pf R₁) f) ◃∙
            ! (ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R₁) f) (ρ (η₀ (fst T₂) b))) ◃∙
            ! (ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ F₁ (str-pf R₁) f)
                (ap fst (app= (psftor-ind-β uC (λ R₂ pe → ∀ p → R₁ psf-≃ fst p) snd) (R₃ , T₂)))) ◃∎
              =ₛ⟨ 1 & 3 & tri-bc◃-rot2-pre (F₁ (str-pf R₁) f) (η₀ (fst T₂) b) ⟩
            ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ F₁ (str-pf R₁) f)
              (ap fst (app= (psftor-ind-β uC (λ R₂ pe → ∀ p → R₁ psf-≃ fst p) snd) (R₃ , T₂))) ◃∙
            ! (ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ F₁ (str-pf R₁) f)
                (ap fst (app= (psftor-ind-β uC (λ R₂ pe → ∀ p → R₁ psf-≃ fst p) snd) (R₃ , T₂)))) ◃∎
              =ₛ₁⟨ !-inv-r
                     (ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ F₁ (str-pf R₁) f)
                       (ap fst (app= (psftor-ind-β uC (λ R₂ pe → ∀ p → R₁ psf-≃ fst p) snd) (R₃ , T₂)))) ⟩
            idp ◃∎ ∎ₛ

    psnat-≃-∙ : {R₁ R₂ R₃ : Psfunctor-nc {{ξB}} {{ξC}}} → R₁ psf-≃ R₂ → R₂ psf-≃ R₃ → R₁ psf-≃ R₃
    η₀ (fst (psnat-≃-∙ T₁ T₂)) = η₀ (pstrans-str (fst T₁) pstrans-∙ pstrans-str (fst T₂))
    η₁ (fst (psnat-≃-∙ T₁ T₂)) = η₁ (pstrans-str (fst T₁) pstrans-∙ pstrans-str (fst T₂))
    coher-unit (fst (psnat-≃-∙ T₁ T₂)) = fst (pstrans-∙-coh-data T₁ T₂)
    coher-assoc (fst (psnat-≃-∙ T₁ T₂)) = snd (pstrans-∙-coh-data T₁ T₂)
    snd (psnat-≃-∙ T₁ T₂) x = univ-ae-∘ uC (_ , (snd T₂ x)) (_ , (snd T₁ x)) 

    abstract
      psnat-≃-∙-β : {R₁ R₂ : Psfunctor-nc {{ξB}} {{ξC}}} {T : R₁ psf-≃ R₂} → psnat-≃-∙ ps-≃-id T == T
      psnat-≃-∙-β {R₁} {R₂} {T} =
        pair= (! (InvModc-to-== (pst-≃ (pstrans-∙-cd.aux-comp {R₂ = R₂} _)
          λ f → η₁-∼-flip (pstrans-∙-cd.aux-sq {R₂ = R₂} _ f)))) prop-has-all-paths-↓  ∙
        app= (psftor-ind-β uC (λ _ pe → ∀ p → R₁ psf-≃ fst p) snd) (R₂ , T)

    module _ {i₃ j₃} {D₀ : Type i₃} {{ξD : BicatStr j₃ D₀}} {R₁ : Psfunctor-nc {{ξB}} {{ξC}}} where

      pstrans-whisk-l-coh-data : {R₂ : Psfunctor-nc {{ξB}} {{ξC}}} (T : R₁ psf-≃ R₂) (G : Psfunctor {{ξC}} {{ξD}})
        → Pst-coh-data (pstrans-whisk-l (pstrans-str (fst T)) (psftor-str G))
      pstrans-whisk-l-coh-data = psftor-ind uC
        (λ R₂ T → (G : Psfunctor {{ξC}} {{ξD}}) → Pst-coh-data (pstrans-whisk-l (pstrans-str (fst T)) (psftor-str G)))
        λ (G : Psfunctor {{ξC}} {{ξD}}) →
          Pstrans-coh-induce (fst (ps-≃-whisk-l {R₁ = R₁} uC {R₂ = R₁} (ps-≃-id {R = R₁}) (psftor-str G)))
          {pstrans-whisk-l (pstrans-str (fst ps-≃-id)) (psftor-str G)}
          (pst-≃ (aux-comp (psftor-str G)) λ f → η₁-∼-flip (aux-sq G f))
        module pstrans-whisk-l-cd where

          aux-comp : (G : Psfunctor-nc {{ξC}} {{ξD}}) (x : B₀) →
            η₀ (fst (ps-≃-whisk-l {R₁ = R₁} uC {R₂ = R₁} (ps-≃-id {R = R₁}) G)) x
              ==
            F₁ (str-pf G) (id₁ (map-pf R₁ x))
          aux-comp G x = 
            ap (λ t → η₀ t x)
              (ap fst (app= (psftor-ind-β uC (λ R₂ _ → ∀ G' → (G' ∘BC-s R₁) psf-≃ (G' ∘BC-s R₂))
                (λ G' → ps-≃-id {R = G' ∘BC-s R₁})) G)) ∙
            ! (F-id₁ (str-pf G) (map-pf R₁ x))

          abstract
            aux-sq : (G : Psfunctor {{ξC}} {{ξD}}) {a b : B₀} (f : hom a b) →
              ! (η₁ (fst (ps-≃-whisk-l uC ps-≃-id (psftor-str G))) f) ◃∙
              ap (λ m → ⟦ ξD ⟧ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f ◻ m) (aux-comp (psftor-str G) a) ◃∙
              (! (F-◻ (str-pf G) (id₁ (map-pf R₁ a)) (F₁ (str-pf R₁) f)) ∙
              ap (F₁ (str-pf G)) (! (ρ (F₁ (str-pf R₁) f)) ∙ lamb (F₁ (str-pf R₁) f)) ∙
              F-◻ (str-pf G) (F₁ (str-pf R₁) f) (id₁ (map-pf R₁ b))) ◃∙
              ! (ap (λ m → ⟦ ξD ⟧ m ◻ ((F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f)) (aux-comp (psftor-str G) b)) ◃∎
                =ₛ
              idp ◃∎
            aux-sq G {a} {b} f = 
              ! (η₁ (fst (ps-≃-whisk-l uC ps-≃-id (psftor-str G))) f) ◃∙
              ap (λ m → ⟦ ξD ⟧ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f ◻ m) (aux-comp (psftor-str G) a) ◃∙
              (! (F-◻ (str-pf G) (id₁ (map-pf R₁ a)) (F₁ (str-pf R₁) f)) ∙
              ap (F₁ (str-pf G)) (! (ρ (F₁ (str-pf R₁) f)) ∙ lamb (F₁ (str-pf R₁) f)) ∙
              F-◻ (str-pf G) (F₁ (str-pf R₁) f) (id₁ (map-pf R₁ b))) ◃∙
              ! (ap (λ m → ⟦ ξD ⟧ m ◻ ((F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f)) (aux-comp (psftor-str G) b)) ◃∎
                =ₛ⟨ 3 & 1 & ap-!!-∙-∘ (λ m → ⟦ ξD ⟧ m ◻ ((F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f)) (λ t → η₀ t b)
                  (ap fst (app= (psftor-ind-β uC (λ R₂ _ → ∀ G' → (G' ∘BC-s R₁) psf-≃ (G' ∘BC-s R₂))
                    (λ G' → ps-≃-id {R = G' ∘BC-s R₁})) (psftor-str G)))
                  (F-id₁ (str-pf G) (map-pf R₁ b)) ⟩
              ! (η₁ (fst (ps-≃-whisk-l uC ps-≃-id (psftor-str G))) f) ◃∙
              ap (λ m → ⟦ ξD ⟧ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f ◻ m) (aux-comp (psftor-str G) a) ◃∙
              (! (F-◻ (str-pf G) (id₁ (map-pf R₁ a)) (F₁ (str-pf R₁) f)) ∙
              ap (F₁ (str-pf G)) (! (ρ (F₁ (str-pf R₁) f)) ∙ lamb (F₁ (str-pf R₁) f)) ∙
              F-◻ (str-pf G) (F₁ (str-pf R₁) f) (id₁ (map-pf R₁ b))) ◃∙
              ap (λ m → ⟦ ξD ⟧ m ◻ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f)
                (F-id₁ (str-pf G) (map-pf R₁ b)) ◃∙
              ! (ap ((λ m → ⟦ ξD ⟧ m ◻ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f) ∘ (λ t → η₀ t b))
                  (ap fst (app=
                    (psftor-ind-β uC (λ R₂ _ → (G' : Psfunctor-nc) → (G' ∘BC-s R₁) psf-≃ (G' ∘BC-s R₂)) (λ G' → ps-≃-id))
                      (psftor-str G)))) ◃∎
                =ₑ⟨ 2 & 1 &
                  (! (F-◻ (str-pf G) (id₁ (map-pf R₁ a)) (F₁ (str-pf R₁) f)) ◃∙
                  ap (F₁ (str-pf G)) (! (ρ (F₁ (str-pf R₁) f)) ∙ lamb (F₁ (str-pf R₁) f)) ◃∙
                  F-◻ (str-pf G) (F₁ (str-pf R₁) f) (id₁ (map-pf R₁ b)) ◃∎)
                  % =ₛ-in (idp {a =
                    ! (F-◻ (str-pf G) (id₁ (map-pf R₁ a)) (F₁ (str-pf R₁) f)) ∙
                    ap (F₁ (str-pf G)) (! (ρ (F₁ (str-pf R₁) f)) ∙ lamb (F₁ (str-pf R₁) f)) ∙
                    F-◻ (str-pf G) (F₁ (str-pf R₁) f) (id₁ (map-pf R₁ b))}) ⟩
              ! (η₁ (fst (ps-≃-whisk-l uC ps-≃-id (psftor-str G))) f) ◃∙
              ap (λ m → ⟦ ξD ⟧ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f ◻ m) (aux-comp (psftor-str G) a) ◃∙
              ! (F-◻ (str-pf G) (id₁ (map-pf R₁ a)) (F₁ (str-pf R₁) f)) ◃∙
              ap (F₁ (str-pf G)) (! (ρ (F₁ (str-pf R₁) f)) ∙ lamb (F₁ (str-pf R₁) f)) ◃∙
              F-◻ (str-pf G) (F₁ (str-pf R₁) f) (id₁ (map-pf R₁ b)) ◃∙
              ap (λ m → ⟦ ξD ⟧ m ◻ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f)
                (F-id₁ (str-pf G) (map-pf R₁ b)) ◃∙
              ! (ap ((λ m → ⟦ ξD ⟧ m ◻ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f) ∘ (λ t → η₀ t b))
                  (ap fst (app=
                    (psftor-ind-β uC (λ R₂ _ → (G' : Psfunctor-nc) → (G' ∘BC-s R₁) psf-≃ (G' ∘BC-s R₂)) (λ G' → ps-≃-id))
                      (psftor-str G)))) ◃∎
                =ₛ⟨ 1 & 1 & ap-∘-∙!◃ (λ m → ⟦ ξD ⟧ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f ◻ m) (λ t → η₀ t a)
                  (ap fst (app=
                    (psftor-ind-β uC (λ R₂ _ → ∀ G' → (G' ∘BC-s R₁) psf-≃ (G' ∘BC-s R₂))
                      (λ G' → ps-≃-id {R = G' ∘BC-s R₁}))
                        (psftor-str G)))
                  (F-id₁ (str-pf G) (map-pf R₁ a)) ⟩
              ! (η₁ (fst (ps-≃-whisk-l uC ps-≃-id (psftor-str G))) f) ◃∙
              ap (λ t → ⟦ ξD ⟧ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f ◻ η₀ t a)
                (ap fst (app=
                  (psftor-ind-β uC (λ R₂ _ → ∀ G' → (G' ∘BC-s R₁) psf-≃ (G' ∘BC-s R₂)) (λ G' → ps-≃-id {R = G' ∘BC-s R₁}))
                    (psftor-str G))) ◃∙
              ! (ap (λ m → ⟦ ξD ⟧ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f ◻ m)
                  (F-id₁ (str-pf G) (map-pf R₁ a))) ◃∙
              ! (F-◻ (str-pf G) (id₁ (map-pf R₁ a)) (F₁ (str-pf R₁) f)) ◃∙
              ap (F₁ (str-pf G)) (! (ρ (F₁ (str-pf R₁) f)) ∙ lamb (F₁ (str-pf R₁) f)) ◃∙
              F-◻ (str-pf G) (F₁ (str-pf R₁) f) (id₁ (map-pf R₁ b)) ◃∙
              ap (λ m → ⟦ ξD ⟧ m ◻ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f)
                (F-id₁ (str-pf G) (map-pf R₁ b)) ◃∙
              ! (ap ((λ m → ⟦ ξD ⟧ m ◻ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f) ∘ (λ t → η₀ t b))
                  (ap fst (app=
                    (psftor-ind-β uC (λ R₂ _ → (G' : Psfunctor-nc) → (G' ∘BC-s R₁) psf-≃ (G' ∘BC-s R₂)) (λ G' → ps-≃-id))
                      (psftor-str G)))) ◃∎
                =ₛ⟨ 0 & 2 & homotopy-naturality-! (λ t → η₁ t f)
                  (ap fst (app=
                    (psftor-ind-β uC (λ R₂ _ → ∀ G' → (G' ∘BC-s R₁) psf-≃ (G' ∘BC-s R₂))
                      (λ G' → ps-≃-id {R = G' ∘BC-s R₁}))
                        (psftor-str G))) ⟩
              ap (λ t → ⟦ ξD ⟧ η₀ t b ◻ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f)
                (ap fst (app=
                  (psftor-ind-β uC (λ R₂ _ → ∀ G' → (G' ∘BC-s R₁) psf-≃ (G' ∘BC-s R₂)) (λ G' → ps-≃-id {R = G' ∘BC-s R₁}))
                    (psftor-str G))) ◃∙
              ! (! (ρ (F₁ (str-pf G) (F₁ (str-pf R₁) f))) ∙
                lamb (F₁ (str-pf G) (F₁ (str-pf R₁) f))) ◃∙
              ! (ap (λ m → ⟦ ξD ⟧ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f ◻ m)
                  (F-id₁ (str-pf G) (map-pf R₁ a))) ◃∙
              ! (F-◻ (str-pf G) (id₁ (map-pf R₁ a)) (F₁ (str-pf R₁) f)) ◃∙
              ap (F₁ (str-pf G)) (! (ρ (F₁ (str-pf R₁) f)) ∙ lamb (F₁ (str-pf R₁) f)) ◃∙
              F-◻ (str-pf G) (F₁ (str-pf R₁) f) (id₁ (map-pf R₁ b)) ◃∙
              ap (λ m → ⟦ ξD ⟧ m ◻ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f)
                (F-id₁ (str-pf G) (map-pf R₁ b)) ◃∙
              ! (ap ((λ m → ⟦ ξD ⟧ m ◻ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f) ∘ (λ t → η₀ t b))
                  (ap fst (app=
                    (psftor-ind-β uC (λ R₂ _ → (G' : Psfunctor-nc) → (G' ∘BC-s R₁) psf-≃ (G' ∘BC-s R₂)) (λ G' → ps-≃-id))
                      (psftor-str G)))) ◃∎
                =ₛ⟨ 4 & 1 & ap-!∙◃ (F₁ (str-pf G)) (ρ (F₁ (str-pf R₁) f)) (lamb (F₁ (str-pf R₁) f)) ⟩
              ap (λ t → ⟦ ξD ⟧ η₀ t b ◻ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f)
                (ap fst (app=
                  (psftor-ind-β uC (λ R₂ _ → ∀ G' → (G' ∘BC-s R₁) psf-≃ (G' ∘BC-s R₂)) (λ G' → ps-≃-id {R = G' ∘BC-s R₁}))
                    (psftor-str G))) ◃∙
              ! (! (ρ (F₁ (str-pf G) (F₁ (str-pf R₁) f))) ∙
                lamb (F₁ (str-pf G) (F₁ (str-pf R₁) f))) ◃∙
              ! (ap (λ m → ⟦ ξD ⟧ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f ◻ m)
                  (F-id₁ (str-pf G) (map-pf R₁ a))) ◃∙
              ! (F-◻ (str-pf G) (id₁ (map-pf R₁ a)) (F₁ (str-pf R₁) f)) ◃∙
              ! (ap (F₁ (str-pf G)) (ρ (F₁ (str-pf R₁) f))) ◃∙
              ap (F₁ (str-pf G)) (lamb (F₁ (str-pf R₁) f)) ◃∙
              F-◻ (str-pf G) (F₁ (str-pf R₁) f) (id₁ (map-pf R₁ b)) ◃∙
              ap (λ m → ⟦ ξD ⟧ m ◻ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f)
                (F-id₁ (str-pf G) (map-pf R₁ b)) ◃∙
              ! (ap ((λ m → ⟦ ξD ⟧ m ◻ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f) ∘ (λ t → η₀ t b))
                  (ap fst (app=
                    (psftor-ind-β uC (λ R₂ _ → (G' : Psfunctor-nc) → (G' ∘BC-s R₁) psf-≃ (G' ∘BC-s R₂)) (λ G' → ps-≃-id))
                      (psftor-str G)))) ◃∎
                =ₛ⟨ 1 & 1 & !-!-∙ (ρ (F₁ (str-pf G) (F₁ (str-pf R₁) f))) (lamb (F₁ (str-pf G) (F₁ (str-pf R₁) f))) ⟩
              ap (λ t → ⟦ ξD ⟧ η₀ t b ◻ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f)
                (ap fst (app=
                  (psftor-ind-β uC (λ R₂ _ → ∀ G' → (G' ∘BC-s R₁) psf-≃ (G' ∘BC-s R₂)) (λ G' → ps-≃-id {R = G' ∘BC-s R₁}))
                    (psftor-str G))) ◃∙
              ! (lamb (F₁ (str-pf G) (F₁ (str-pf R₁) f))) ◃∙
              ρ (F₁ (str-pf G) (F₁ (str-pf R₁) f)) ◃∙
              ! (ap (λ m → ⟦ ξD ⟧ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f ◻ m)
                  (F-id₁ (str-pf G) (map-pf R₁ a))) ◃∙
              ! (F-◻ (str-pf G) (id₁ (map-pf R₁ a)) (F₁ (str-pf R₁) f)) ◃∙
              ! (ap (F₁ (str-pf G)) (ρ (F₁ (str-pf R₁) f))) ◃∙
              ap (F₁ (str-pf G)) (lamb (F₁ (str-pf R₁) f)) ◃∙
              F-◻ (str-pf G) (F₁ (str-pf R₁) f) (id₁ (map-pf R₁ b)) ◃∙
              ap (λ m → ⟦ ξD ⟧ m ◻ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f)
                (F-id₁ (str-pf G) (map-pf R₁ b)) ◃∙
              ! (ap ((λ m → ⟦ ξD ⟧ m ◻ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f) ∘ (λ t → η₀ t b))
                  (ap fst (app=
                    (psftor-ind-β uC (λ R₂ _ → (G' : Psfunctor-nc) → (G' ∘BC-s R₁) psf-≃ (G' ∘BC-s R₂)) (λ G' → ps-≃-id))
                      (psftor-str G)))) ◃∎
                =ₛ⟨ 2 & 4 & !ₛ (F-ρ-rot-!3 (str-pf G) (F₁ (str-pf R₁) f)) ⟩ 
              ap (λ t → ⟦ ξD ⟧ η₀ t b ◻ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f)
                (ap fst (app=
                  (psftor-ind-β uC (λ R₂ _ → ∀ G' → (G' ∘BC-s R₁) psf-≃ (G' ∘BC-s R₂)) (λ G' → ps-≃-id {R = G' ∘BC-s R₁}))
                    (psftor-str G))) ◃∙
              ! (lamb (F₁ (str-pf G) (F₁ (str-pf R₁) f))) ◃∙
              ap (F₁ (str-pf G)) (lamb (F₁ (str-pf R₁) f)) ◃∙
              F-◻ (str-pf G) (F₁ (str-pf R₁) f) (id₁ (map-pf R₁ b)) ◃∙
              ap (λ m → ⟦ ξD ⟧ m ◻ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f)
                (F-id₁ (str-pf G) (map-pf R₁ b)) ◃∙
              ! (ap ((λ m → ⟦ ξD ⟧ m ◻ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f) ∘ (λ t → η₀ t b))
                  (ap fst (app=
                    (psftor-ind-β uC (λ R₂ _ → (G' : Psfunctor-nc) → (G' ∘BC-s R₁) psf-≃ (G' ∘BC-s R₂)) (λ G' → ps-≃-id))
                      (psftor-str G)))) ◃∎
                =ₛ⟨ 1 & 4 & F-λ-rot (str-pf G) (F₁ (str-pf R₁) f) ⟩
              ap (λ t → ⟦ ξD ⟧ η₀ t b ◻ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f)
                (ap fst (app=
                  (psftor-ind-β uC (λ R₂ _ → ∀ G' → (G' ∘BC-s R₁) psf-≃ (G' ∘BC-s R₂)) (λ G' → ps-≃-id {R = G' ∘BC-s R₁}))
                    (psftor-str G))) ◃∙
              ! (ap ((λ m → ⟦ ξD ⟧ m ◻ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f) ∘ (λ t → η₀ t b))
                  (ap fst (app=
                    (psftor-ind-β uC (λ R₂ _ → (G' : Psfunctor-nc) → (G' ∘BC-s R₁) psf-≃ (G' ∘BC-s R₂)) (λ G' → ps-≃-id))
                      (psftor-str G)))) ◃∎
                =ₛ₁⟨ !-inv-r
                       (ap ((λ m → ⟦ ξD ⟧ m ◻ (F₁ (str-pf G) ∘ F₁ (str-pf R₁)) f) ∘ (λ t → η₀ t b))
                         (ap fst (app=
                           (psftor-ind-β uC (λ R₂ _ → (G' : Psfunctor-nc) → (G' ∘BC-s R₁) psf-≃ (G' ∘BC-s R₂))
                             (λ G' → ps-≃-id))
                               (psftor-str G)))) ⟩
              idp ◃∎ ∎ₛ

      psnat-≃-whisk-l : {R₂ : Psfunctor-nc {{ξB}} {{ξC}}} → R₁ psf-≃ R₂ →
        (G : Psfunctor {{ξC}} {{ξD}}) → (psftor-str G ∘BC-s R₁) psf-≃ (psftor-str G ∘BC-s R₂)
      η₀ (fst (psnat-≃-whisk-l T G)) = η₀ (pstrans-whisk-l (pstrans-str (fst T)) (psftor-str G))
      η₁ (fst (psnat-≃-whisk-l T G)) = η₁ (pstrans-whisk-l (pstrans-str (fst T)) (psftor-str G))
      coher-unit (fst (psnat-≃-whisk-l T G)) = fst (pstrans-whisk-l-coh-data T G)
      coher-assoc (fst (psnat-≃-whisk-l T G)) = snd (pstrans-whisk-l-coh-data T G)
      snd (psnat-≃-whisk-l T G) b = univ-pf-ae uC {R = psftor-str G} (η₀ (fst T) b , snd T b)

      abstract
        psnat-≃-whisk-l-β : {R₂ : Psfunctor-nc {{ξB}} {{ξC}}} {T : R₁ psf-≃ R₂} (G : Psfunctor {{ξC}} {{ξD}})
          → psnat-≃-whisk-l ps-≃-id G == ps-≃-id 
        psnat-≃-whisk-l-β {R₂} {T} G = 
          pair= (! (InvModc-to-== (pst-≃ (pstrans-whisk-l-cd.aux-comp {R₂ = R₂} (psftor-str G))
            λ f → η₁-∼-flip (pstrans-whisk-l-cd.aux-sq {R₂ = R₂} G f)))) prop-has-all-paths-↓  ∙
          app= (psftor-ind-β uC (λ R pe → ∀ G' → (G' ∘BC-s R₁) psf-≃ (G' ∘BC-s R)) (λ _ → ps-≃-id)) (psftor-str G)

    module _ {i₃ j₃} {D₀ : Type i₃} {{ξD : BicatStr j₃ D₀}} {R₁ : Psfunctor-nc {{ξB}} {{ξC}}} where

      pstrans-whisk-r-coh-data : {R₂ : Psfunctor-nc {{ξB}} {{ξC}}} (T : R₁ psf-≃ R₂) (G : Psfunctor-nc {{ξD}} {{ξB}})
        → Pst-coh-data (pstrans-whisk-r (pstrans-str (fst T)) G)
      pstrans-whisk-r-coh-data = psftor-ind uC
        (λ R₂ T → (G : Psfunctor-nc {{ξD}} {{ξB}}) → Pst-coh-data (pstrans-whisk-r (pstrans-str (fst T)) G))
        λ (G : Psfunctor-nc {{ξD}} {{ξB}}) →
          Pstrans-coh-induce (fst (ps-≃-whisk-r {R₁ = R₁} uC {R₂ = R₁} (ps-≃-id {R = R₁}) G))
          {pstrans-whisk-r (pstrans-str (fst ps-≃-id)) G}
          (pst-≃ (aux-comp G) λ f → η₁-∼-flip (aux-sq G f))
        module pstrans-whisk-r-cd where

          aux-comp : (G : Psfunctor-nc {{ξD}} {{ξB}}) (x : D₀) →
            η₀ (fst (ps-≃-whisk-r {R₁ = R₁} uC {R₂ = R₁} ps-≃-id G)) x == id₁ (map-pf R₁ (map-pf G x))
          aux-comp G x = 
            ap (λ t → η₀ t x)
              (ap fst (app=
                (psftor-ind-β uC (λ R₂ _ → ∀ G' → (R₁ ∘BC-s G') psf-≃ (R₂ ∘BC-s G'))
                  (λ G' → ps-≃-id {R = R₁ ∘BC-s G'})) G))
          
          abstract
            aux-sq : (G : Psfunctor-nc {{ξD}} {{ξB}}) {a b : D₀} (f : hom a b) →
              (! (η₁ (fst (ps-≃-whisk-r uC ps-≃-id G)) f) ◃∙
              ap (λ m → ⟦ ξC ⟧ (F₁ (str-pf R₁) ∘ F₁ (str-pf G)) f ◻ m) (aux-comp G a) ◃∙
              (! (ρ (F₁ (str-pf R₁) (F₁ (str-pf G) f))) ∙ lamb (F₁ (str-pf R₁) (F₁ (str-pf G) f))) ◃∙
              ! (ap (λ m → ⟦ ξC ⟧ m ◻ ((F₁ (str-pf R₁) ∘ F₁ (str-pf G)) f)) (aux-comp G b)) ◃∎)
                =ₛ
              idp ◃∎
            aux-sq G {a} {b} f = 
              ! (η₁ (fst (ps-≃-whisk-r uC ps-≃-id G)) f) ◃∙
              ap (λ m → ⟦ ξC ⟧ (F₁ (str-pf R₁) ∘ F₁ (str-pf G)) f ◻ m) (aux-comp G a) ◃∙
              (! (ρ (F₁ (str-pf R₁) (F₁ (str-pf G) f))) ∙ lamb (F₁ (str-pf R₁) (F₁ (str-pf G) f))) ◃∙
              ! (ap (λ m → ⟦ ξC ⟧ m ◻ ((F₁ (str-pf R₁) ∘ F₁ (str-pf G)) f)) (aux-comp G b)) ◃∎
                =ₛ₁⟨ 3 & 1 & ap ! (∘-ap (λ m → ⟦ ξC ⟧ m ◻ ((F₁ (str-pf R₁) ∘ F₁ (str-pf G)) f)) (λ t → η₀ t b)
                  (ap fst (app=
                    (psftor-ind-β uC (λ R₂ _ → ∀ G' → (R₁ ∘BC-s G') psf-≃ (R₂ ∘BC-s G'))
                      (λ G' → ps-≃-id {R = R₁ ∘BC-s G'})) G))) ⟩
              ! (η₁ (fst (ps-≃-whisk-r uC ps-≃-id G)) f) ◃∙
              ap (λ m → ⟦ ξC ⟧ (F₁ (str-pf R₁) ∘ F₁ (str-pf G)) f ◻ m) (aux-comp G a) ◃∙
              (! (ρ (F₁ (str-pf R₁) (F₁ (str-pf G) f))) ∙ lamb (F₁ (str-pf R₁) (F₁ (str-pf G) f))) ◃∙
              ! (ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ ((F₁ (str-pf R₁) ∘ F₁ (str-pf G)) f))
                  (ap fst (app=
                    (psftor-ind-β uC (λ R₂ _ → ∀ G' → (R₁ ∘BC-s G') psf-≃ (R₂ ∘BC-s G'))
                      (λ G' → ps-≃-id {R = R₁ ∘BC-s G'})) G))) ◃∎
                =ₑ⟨ 2 & 1 & (! (ρ (F₁ (str-pf R₁) (F₁ (str-pf G) f))) ◃∙ lamb (F₁ (str-pf R₁) (F₁ (str-pf G) f)) ◃∎)
                  % =ₛ-in (idp {a =
                    ! (ρ (F₁ (str-pf R₁) (F₁ (str-pf G) f))) ∙ lamb (F₁ (str-pf R₁) (F₁ (str-pf G) f))}) ⟩
              ! (η₁ (fst (ps-≃-whisk-r uC ps-≃-id G)) f) ◃∙
              ap (λ m → ⟦ ξC ⟧ (F₁ (str-pf R₁) ∘ F₁ (str-pf G)) f ◻ m) (aux-comp G a) ◃∙
              ! (ρ (F₁ (str-pf R₁) (F₁ (str-pf G) f))) ◃∙
              lamb (F₁ (str-pf R₁) (F₁ (str-pf G) f)) ◃∙
              ! (ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ ((F₁ (str-pf R₁) ∘ F₁ (str-pf G)) f))
                  (ap fst (app=
                    (psftor-ind-β uC (λ R₂ _ → ∀ G' → (R₁ ∘BC-s G') psf-≃ (R₂ ∘BC-s G'))
                      (λ G' → ps-≃-id {R = R₁ ∘BC-s G'})) G))) ◃∎
                =ₛ₁⟨ 1 & 1 & ∘-ap (λ m → ⟦ ξC ⟧ (F₁ (str-pf R₁) ∘ F₁ (str-pf G)) f ◻ m) (λ t → η₀ t a)
                  (ap fst (app=
                    (psftor-ind-β uC (λ R₂ _ → ∀ G' → (R₁ ∘BC-s G') psf-≃ (R₂ ∘BC-s G'))
                      (λ G' → ps-≃-id {R = R₁ ∘BC-s G'})) G)) ⟩
              ! (η₁ (fst (ps-≃-whisk-r uC ps-≃-id G)) f) ◃∙
              ap (λ t → ⟦ ξC ⟧ (F₁ (str-pf R₁) ∘ F₁ (str-pf G)) f ◻ η₀ t a)
                (ap fst (app=
                  (psftor-ind-β uC (λ R₂ _ → ∀ G' → (R₁ ∘BC-s G') psf-≃ (R₂ ∘BC-s G'))
                    (λ G' → ps-≃-id {R = R₁ ∘BC-s G'})) G)) ◃∙
              ! (ρ (F₁ (str-pf R₁) (F₁ (str-pf G) f))) ◃∙
              lamb (F₁ (str-pf R₁) (F₁ (str-pf G) f)) ◃∙
              ! (ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ ((F₁ (str-pf R₁) ∘ F₁ (str-pf G)) f))
                  (ap fst (app=
                    (psftor-ind-β uC (λ R₂ _ → ∀ G' → (R₁ ∘BC-s G') psf-≃ (R₂ ∘BC-s G'))
                      (λ G' → ps-≃-id {R = R₁ ∘BC-s G'})) G))) ◃∎
                =ₛ⟨ 0 & 2 & homotopy-naturality-! (λ t → η₁ t f)
                  (ap fst (app=
                    (psftor-ind-β uC (λ R₂ _ → ∀ G' → (R₁ ∘BC-s G') psf-≃ (R₂ ∘BC-s G'))
                      (λ G' → ps-≃-id {R = R₁ ∘BC-s G'})) G)) ⟩
              ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ (F₁ (str-pf R₁) ∘ F₁ (str-pf G)) f)
                (ap fst (app=
                  (psftor-ind-β uC (λ R₂ _ → ∀ G' → (R₁ ∘BC-s G') psf-≃ (R₂ ∘BC-s G'))
                    (λ G' → ps-≃-id {R = R₁ ∘BC-s G'})) G)) ◃∙
              ! (! (ρ (F₁ (str-pf R₁) (F₁ (str-pf G) f))) ∙ lamb (F₁ (str-pf R₁) (F₁ (str-pf G) f))) ◃∙
              ! (ρ (F₁ (str-pf R₁) (F₁ (str-pf G) f))) ◃∙
              lamb (F₁ (str-pf R₁) (F₁ (str-pf G) f)) ◃∙
              ! (ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ ((F₁ (str-pf R₁) ∘ F₁ (str-pf G)) f))
                  (ap fst (app=
                    (psftor-ind-β uC (λ R₂ _ → ∀ G' → (R₁ ∘BC-s G') psf-≃ (R₂ ∘BC-s G'))
                      (λ G' → ps-≃-id {R = R₁ ∘BC-s G'})) G))) ◃∎
                =ₛ⟨ 1 & 1 & !-!-∙ (ρ (F₁ (str-pf R₁) (F₁ (str-pf G) f))) (lamb (F₁ (str-pf R₁) (F₁ (str-pf G) f))) ⟩
              ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ (F₁ (str-pf R₁) ∘ F₁ (str-pf G)) f)
                (ap fst (app=
                  (psftor-ind-β uC (λ R₂ _ → ∀ G' → (R₁ ∘BC-s G') psf-≃ (R₂ ∘BC-s G'))
                    (λ G' → ps-≃-id {R = R₁ ∘BC-s G'})) G)) ◃∙
              ! (lamb (F₁ (str-pf R₁) (F₁ (str-pf G) f))) ◃∙
              ρ (F₁ (str-pf R₁) (F₁ (str-pf G) f)) ◃∙
              ! (ρ (F₁ (str-pf R₁) (F₁ (str-pf G) f))) ◃∙
              lamb (F₁ (str-pf R₁) (F₁ (str-pf G) f)) ◃∙
              ! (ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ ((F₁ (str-pf R₁) ∘ F₁ (str-pf G)) f))
                  (ap fst (app=
                    (psftor-ind-β uC (λ R₂ _ → ∀ G' → (R₁ ∘BC-s G') psf-≃ (R₂ ∘BC-s G'))
                      (λ G' → ps-≃-id {R = R₁ ∘BC-s G'})) G))) ◃∎
                =ₛ⟨ 2 & 2 & !-inv-r◃
                  {x = F₁ (str-pf R₁) (F₁ (str-pf G) f)}
                  {y = ⟦ ξC ⟧ F₁ (str-pf R₁) (F₁ (str-pf G) f) ◻ id₁ (map-pf R₁ (map-pf G a))}
                    (ρ (F₁ (str-pf R₁) (F₁ (str-pf G) f))) ⟩
              ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ (F₁ (str-pf R₁) ∘ F₁ (str-pf G)) f)
                (ap fst (app=
                  (psftor-ind-β uC (λ R₂ _ → ∀ G' → (R₁ ∘BC-s G') psf-≃ (R₂ ∘BC-s G'))
                    (λ G' → ps-≃-id {R = R₁ ∘BC-s G'})) G)) ◃∙
              ! (lamb (F₁ (str-pf R₁) (F₁ (str-pf G) f))) ◃∙
              lamb (F₁ (str-pf R₁) (F₁ (str-pf G) f)) ◃∙
              ! (ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ ((F₁ (str-pf R₁) ∘ F₁ (str-pf G)) f))
                  (ap fst (app=
                    (psftor-ind-β uC (λ R₂ _ → ∀ G' → (R₁ ∘BC-s G') psf-≃ (R₂ ∘BC-s G'))
                      (λ G' → ps-≃-id {R = R₁ ∘BC-s G'})) G))) ◃∎
                =ₛ⟨ 1 & 2 & !-inv-l◃ (lamb (F₁ (str-pf R₁) (F₁ (str-pf G) f))) ⟩
              ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ (F₁ (str-pf R₁) ∘ F₁ (str-pf G)) f)
                (ap fst (app=
                  (psftor-ind-β uC (λ R₂ _ → ∀ G' → (R₁ ∘BC-s G') psf-≃ (R₂ ∘BC-s G'))
                    (λ G' → ps-≃-id {R = R₁ ∘BC-s G'})) G)) ◃∙
              ! (ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ ((F₁ (str-pf R₁) ∘ F₁ (str-pf G)) f))
                  (ap fst (app=
                    (psftor-ind-β uC (λ R₂ _ → ∀ G' → (R₁ ∘BC-s G') psf-≃ (R₂ ∘BC-s G'))
                      (λ G' → ps-≃-id {R = R₁ ∘BC-s G'})) G))) ◃∎
                =ₛ₁⟨ !-inv-r
                       (ap (λ t → ⟦ ξC ⟧ η₀ t b ◻ ((F₁ (str-pf R₁) ∘ F₁ (str-pf G)) f))
                         (ap fst (app=
                           (psftor-ind-β uC (λ R₂ _ → ∀ G' → (R₁ ∘BC-s G') psf-≃ (R₂ ∘BC-s G'))
                             (λ G' → ps-≃-id {R = R₁ ∘BC-s G'})) G))) ⟩
              idp ◃∎ ∎ₛ

      psnat-≃-whisk-r : {R₂ : Psfunctor-nc {{ξB}} {{ξC}}} → R₁ psf-≃ R₂ →
        (G : Psfunctor-nc {{ξD}} {{ξB}}) → (R₁ ∘BC-s G) psf-≃ (R₂ ∘BC-s G)
      η₀ (fst (psnat-≃-whisk-r T G)) = η₀ (pstrans-whisk-r (pstrans-str (fst T)) G)
      η₁ (fst (psnat-≃-whisk-r T G)) = η₁ (pstrans-whisk-r (pstrans-str (fst T)) G)
      coher-unit (fst (psnat-≃-whisk-r T G)) = fst (pstrans-whisk-r-coh-data T G)
      coher-assoc (fst (psnat-≃-whisk-r T G)) = snd (pstrans-whisk-r-coh-data T G)
      snd (psnat-≃-whisk-r T G) b = snd T (map-pf G b)

      abstract
        psnat-≃-whisk-r-β : {R₂ : Psfunctor-nc {{ξB}} {{ξC}}} {T : R₁ psf-≃ R₂} (G : Psfunctor-nc {{ξD}} {{ξB}})
          → psnat-≃-whisk-r ps-≃-id G == ps-≃-id 
        psnat-≃-whisk-r-β {R₂} {T} G = 
          pair= (! (InvModc-to-== (pst-≃ (pstrans-whisk-r-cd.aux-comp {R₂ = R₂} G)
            λ f → η₁-∼-flip (pstrans-whisk-r-cd.aux-sq {R₂ = R₂} G f)))) prop-has-all-paths-↓  ∙
          app= (psftor-ind-β uC (λ R pe → ∀ G' → (R₁ ∘BC-s G') psf-≃ (R ∘BC-s G')) (λ _ → ps-≃-id)) G

  infixr 10 _uvpsnat-≃-∙_
  _uvpsnat-≃-∙_ : {{is-univ-bc-inst {{ξC}}}} → {R₁ R₂ R₃ : Psfunctor-nc {{ξB}} {{ξC}}}
    → R₁ psf-≃ R₂ → R₂ psf-≃ R₃ → R₁ psf-≃ R₃
  _uvpsnat-≃-∙_ {{uC}} {R₁} pe p = psnat-≃-∙ (λ a b → uC {a} {b}) pe p

  module _ {i₃ j₃} {D₀ : Type i₃} {{ξD : BicatStr j₃ D₀}} {R₁ R₂ : Psfunctor-nc {{ξB}} {{ξC}}} where

    uvpsnat-≃-whisk-l : {{is-univ-bc-inst {{ξC}}}} → R₁ psf-≃ R₂ →
      (G : Psfunctor {{ξC}} {{ξD}}) → ((psftor-str G) ∘BC-s R₁) psf-≃ ((psftor-str G) ∘BC-s R₂)
    uvpsnat-≃-whisk-l {{uC}} T G = psnat-≃-whisk-l (λ a b → uC {a} {b}) T G

    uvpsnat-≃-whisk-r : {{is-univ-bc-inst {{ξC}}}} → R₁ psf-≃ R₂ →
      (G : Psfunctor-nc {{ξD}} {{ξB}}) → (R₁ ∘BC-s G) psf-≃ (R₂ ∘BC-s G)
    uvpsnat-≃-whisk-r {{uC}} T G = psnat-≃-whisk-r (λ a b → uC {a} {b}) T G
