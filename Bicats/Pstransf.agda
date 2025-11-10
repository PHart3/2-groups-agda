{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.wild-cats.WildCats renaming
  (hom to homW; id₁ to id₁W; ρ to ρW; lamb to lambW; α to αW)
open import Bicat-wild
open import Bicategory
open import Bicat-coher

module Pstransf where

open BicatStr {{...}}
open Psfunctor
open PsfunctorStr

module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂} {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}}  where

  -- pseudotransformations
  record Pstrans (R S : Psfunctor {{ξB}} {{ξC}}) : Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
    field
      η₀ : (a : B₀) → hom (map-pf R a) (map-pf S a)
      η₁ : {a b : B₀} (f : hom a b) → F₁ (str-pf S) f ◻ η₀ a == ⟦ ξC ⟧ η₀ b ◻ F₁ (str-pf R) f
      coher-unit : {a : B₀} →
        lamb (η₀ a) ∙
        ap (λ m → m ◻ η₀ a) (! (F-id₁ (str-pf S) a)) ∙
        η₁ (id₁ a) ∙
        ap (λ m → η₀ a ◻ m) (F-id₁ (str-pf R) a)
          ==
        ρ (η₀ a)
      coher-assoc : {a b c : B₀} (f : hom a b) (g : hom b c) →
        ! (η₁ (⟦ ξB ⟧ g ◻ f)) ∙
        ap (λ m → m ◻ η₀ a) (F-◻ (str-pf S) f g) ∙
        ! (α (F₁ (str-pf S) g) (F₁ (str-pf S) f) (η₀ a)) ∙
        ap (λ m → F₁ (str-pf S) g ◻ m) (η₁ f) ∙
        α (F₁ (str-pf S) g) (η₀ b) (F₁ (str-pf R) f) ∙
        ap (λ m → m ◻ (F₁ (str-pf R) f)) (η₁ g) ∙
        ! (α (η₀ c) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ∙
        ! (ap (λ m → η₀ c ◻ m) (F-◻ (str-pf R) f g))
          ==
        idp

  open Pstrans

  Pstrans-id : (R : Psfunctor {{ξB}} {{ξC}}) → Pstrans R R
  η₀ (Pstrans-id R) a = id₁ (map-pf R a)
  η₁ (Pstrans-id R) f = ! (ρ (F₁ (str-pf R) f)) ∙ lamb (F₁ (str-pf R) f)
  coher-unit (Pstrans-id R) {a} = =ₛ-out $
    lamb (id₁ (map-pf R a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R a)) (! (F-id₁ (str-pf R) a)) ◃∙
    (! (ρ (F₁ (str-pf R) (id₁ a))) ∙
    lamb (F₁ (str-pf R) (id₁ a))) ◃∙
    ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R a) ◻ m) (F-id₁ (str-pf R) a) ◃∎
      =ₛ⟨ 2 & 1 & apCommSq2◃-rev (λ x → ! (ρ x) ∙ lamb x) (F-id₁ (str-pf R) a) ⟩
    lamb (id₁ (map-pf R a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R a)) (! (F-id₁ (str-pf R) a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R a)) (F-id₁ (str-pf R) a) ◃∙
    (! (ρ (id₁ (map-pf R a))) ∙ lamb (id₁ (map-pf R a))) ◃∙
    ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R a) ◻ m) (F-id₁ (str-pf R) a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R a) ◻ m) (F-id₁ (str-pf R) a) ◃∎
      =ₛ₁⟨ 3 & 1 & ap (λ p → ! (ρ (id₁ (map-pf R a))) ∙ p) lamb-ρ-id₁-bc ∙ !-inv-l (ρ (id₁ (map-pf R a))) ⟩
    lamb (id₁ (map-pf R a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R a)) (! (F-id₁ (str-pf R) a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R a)) (F-id₁ (str-pf R) a) ◃∙
    idp ◃∙
    ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R a) ◻ m) (F-id₁ (str-pf R) a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R a) ◻ m) (F-id₁ (str-pf R) a) ◃∎
      =ₛ₁⟨ 3 & 3 & !-inv-l (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R a) ◻ m) (F-id₁ (str-pf R) a)) ⟩
    lamb (id₁ (map-pf R a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R a)) (! (F-id₁ (str-pf R) a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R a)) (F-id₁ (str-pf R) a) ◃∙
    idp ◃∎
      =ₛ₁⟨ 1 & 1 & ap-! (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R a)) (F-id₁ (str-pf R) a) ⟩
    lamb (id₁ (map-pf R a)) ◃∙
    ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R a)) (F-id₁ (str-pf R) a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R a)) (F-id₁ (str-pf R) a) ◃∙
    idp ◃∎
      =ₛ₁⟨ 1 & 2 & !-inv-l (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R a)) (F-id₁ (str-pf R) a)) ⟩
    lamb (id₁ (map-pf R a)) ◃∙
    idp ◃∙
    idp ◃∎
      =ₛ₁⟨ ∙-unit-r (lamb (id₁ (map-pf R a))) ∙ lamb-ρ-id₁-bc ⟩
    ρ (id₁ (map-pf R a)) ◃∎ ∎ₛ
  coher-assoc (Pstrans-id R) {a} {b} {c} f g = =ₛ-out $
    ! (! (ρ (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ∙ lamb (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R a)) (F-◻ (str-pf R) f g) ◃∙
    ! (α (F₁ (str-pf R) g) (F₁ (str-pf R) f) (id₁ (map-pf R a))) ◃∙
    ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (! (ρ (F₁ (str-pf R) f)) ∙ lamb (F₁ (str-pf R) f)) ◃∙
    α (F₁ (str-pf R) g) (id₁ (map-pf R b)) (F₁ (str-pf R) f) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (! (ρ (F₁ (str-pf R) g)) ∙ lamb (F₁ (str-pf R) g)) ◃∙
    ! (α (id₁ (map-pf R c)) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ◃∙
    ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R c) ◻ m) (F-◻ (str-pf R) f g)) ◃∎
      =ₛ⟨ 0 & 1 & hmtpy-nat-!◃ (λ x → ! (ρ x) ∙ lamb x) (F-◻ (str-pf R) f g) ⟩
    ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R c) ◻ m) (F-◻ (str-pf R) f g) ◃∙
    ! (! (ρ (⟦ ξC ⟧ F₁ (str-pf R) g ◻ F₁ (str-pf R) f)) ∙ lamb (⟦ ξC ⟧ F₁ (str-pf R) g ◻ F₁ (str-pf R) f)) ◃∙
    ! (ap (λ m → ⟦ ξC ⟧ m ◻ (id₁ (map-pf R a))) (F-◻ (str-pf R) f g)) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R a)) (F-◻ (str-pf R) f g) ◃∙
    ! (α (F₁ (str-pf R) g) (F₁ (str-pf R) f) (id₁ (map-pf R a))) ◃∙
    ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (! (ρ (F₁ (str-pf R) f)) ∙ lamb (F₁ (str-pf R) f)) ◃∙
    α (F₁ (str-pf R) g) (id₁ (map-pf R b)) (F₁ (str-pf R) f) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (! (ρ (F₁ (str-pf R) g)) ∙ lamb (F₁ (str-pf R) g)) ◃∙
    ! (α (id₁ (map-pf R c)) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ◃∙
    ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R c) ◻ m) (F-◻ (str-pf R) f g)) ◃∎
      =ₛ₁⟨ 2 & 2 & !-inv-l (ap (λ m → ⟦ ξC ⟧ m ◻ (id₁ (map-pf R a))) (F-◻ (str-pf R) f g)) ⟩
    ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R c) ◻ m) (F-◻ (str-pf R) f g) ◃∙
    ! (! (ρ (⟦ ξC ⟧ F₁ (str-pf R) g ◻ F₁ (str-pf R) f)) ∙ lamb (⟦ ξC ⟧ F₁ (str-pf R) g ◻ F₁ (str-pf R) f)) ◃∙
    idp ◃∙
    ! (α (F₁ (str-pf R) g) (F₁ (str-pf R) f) (id₁ (map-pf R a))) ◃∙
    ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (! (ρ (F₁ (str-pf R) f)) ∙ lamb (F₁ (str-pf R) f)) ◃∙
    α (F₁ (str-pf R) g) (id₁ (map-pf R b)) (F₁ (str-pf R) f) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (! (ρ (F₁ (str-pf R) g)) ∙ lamb (F₁ (str-pf R) g)) ◃∙
    ! (α (id₁ (map-pf R c)) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ◃∙
    ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R c) ◻ m) (F-◻ (str-pf R) f g)) ◃∎
      =ₛ⟨ 5 & 1 & tri-bc◃ (F₁ (str-pf R) f) (F₁ (str-pf R) g) ⟩
    ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R c) ◻ m) (F-◻ (str-pf R) f g) ◃∙
    ! (! (ρ (⟦ ξC ⟧ F₁ (str-pf R) g ◻ F₁ (str-pf R) f)) ∙ lamb (⟦ ξC ⟧ F₁ (str-pf R) g ◻ F₁ (str-pf R) f)) ◃∙
    idp ◃∙
    ! (α (F₁ (str-pf R) g) (F₁ (str-pf R) f) (id₁ (map-pf R a))) ◃∙
    ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (! (ρ (F₁ (str-pf R) f)) ∙ lamb (F₁ (str-pf R) f)) ◃∙
    ! (ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (lamb (F₁ (str-pf R) f))) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (ρ (F₁ (str-pf R) g)) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (! (ρ (F₁ (str-pf R) g)) ∙ lamb (F₁ (str-pf R) g)) ◃∙
    ! (α (id₁ (map-pf R c)) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ◃∙
    ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R c) ◻ m) (F-◻ (str-pf R) f g)) ◃∎
      =ₛ⟨ 7 & 1 & ap-!∙◃ (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (ρ (F₁ (str-pf R) g)) (lamb (F₁ (str-pf R) g)) ⟩
    ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R c) ◻ m) (F-◻ (str-pf R) f g) ◃∙
    ! (! (ρ (⟦ ξC ⟧ F₁ (str-pf R) g ◻ F₁ (str-pf R) f)) ∙ lamb (⟦ ξC ⟧ F₁ (str-pf R) g ◻ F₁ (str-pf R) f)) ◃∙
    idp ◃∙
    ! (α (F₁ (str-pf R) g) (F₁ (str-pf R) f) (id₁ (map-pf R a))) ◃∙
    ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (! (ρ (F₁ (str-pf R) f)) ∙ lamb (F₁ (str-pf R) f)) ◃∙
    ! (ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (lamb (F₁ (str-pf R) f))) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (ρ (F₁ (str-pf R) g)) ◃∙
    ! (ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (ρ (F₁ (str-pf R) g))) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (lamb (F₁ (str-pf R) g)) ◃∙
    ! (α (id₁ (map-pf R c)) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ◃∙
    ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R c) ◻ m) (F-◻ (str-pf R) f g)) ◃∎
      =ₛ₁⟨ 6 & 2 & !-inv-r (ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (ρ (F₁ (str-pf R) g))) ⟩
    ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R c) ◻ m) (F-◻ (str-pf R) f g) ◃∙
    ! (! (ρ (⟦ ξC ⟧ F₁ (str-pf R) g ◻ F₁ (str-pf R) f)) ∙ lamb (⟦ ξC ⟧ F₁ (str-pf R) g ◻ F₁ (str-pf R) f)) ◃∙
    idp ◃∙
    ! (α (F₁ (str-pf R) g) (F₁ (str-pf R) f) (id₁ (map-pf R a))) ◃∙
    ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (! (ρ (F₁ (str-pf R) f)) ∙ lamb (F₁ (str-pf R) f)) ◃∙
    ! (ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (lamb (F₁ (str-pf R) f))) ◃∙
    idp ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (lamb (F₁ (str-pf R) g)) ◃∙
    ! (α (id₁ (map-pf R c)) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ◃∙
    ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R c) ◻ m) (F-◻ (str-pf R) f g)) ◃∎
      =ₛ⟨ 4 & 1 & ap-!∙◃ (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (ρ (F₁ (str-pf R) f)) (lamb (F₁ (str-pf R) f)) ⟩
    ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R c) ◻ m) (F-◻ (str-pf R) f g) ◃∙
    ! (! (ρ (⟦ ξC ⟧ F₁ (str-pf R) g ◻ F₁ (str-pf R) f)) ∙ lamb (⟦ ξC ⟧ F₁ (str-pf R) g ◻ F₁ (str-pf R) f)) ◃∙
    idp ◃∙
    ! (α (F₁ (str-pf R) g) (F₁ (str-pf R) f) (id₁ (map-pf R a))) ◃∙
    ! (ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (ρ (F₁ (str-pf R) f))) ◃∙
    ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (lamb (F₁ (str-pf R) f)) ◃∙
    ! (ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (lamb (F₁ (str-pf R) f))) ◃∙
    idp ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (lamb (F₁ (str-pf R) g)) ◃∙
    ! (α (id₁ (map-pf R c)) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ◃∙
    ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R c) ◻ m) (F-◻ (str-pf R) f g)) ◃∎
      =ₛ₁⟨ 5 & 2 & !-inv-r (ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (lamb (F₁ (str-pf R) f))) ⟩
    ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R c) ◻ m) (F-◻ (str-pf R) f g) ◃∙
    ! (! (ρ (⟦ ξC ⟧ F₁ (str-pf R) g ◻ F₁ (str-pf R) f)) ∙ lamb (⟦ ξC ⟧ F₁ (str-pf R) g ◻ F₁ (str-pf R) f)) ◃∙
    idp ◃∙
    ! (α (F₁ (str-pf R) g) (F₁ (str-pf R) f) (id₁ (map-pf R a))) ◃∙
    ! (ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (ρ (F₁ (str-pf R) f))) ◃∙
    idp ◃∙
    idp ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (lamb (F₁ (str-pf R) g)) ◃∙
    ! (α (id₁ (map-pf R c)) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ◃∙
    ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R c) ◻ m) (F-◻ (str-pf R) f g)) ◃∎
      =ₛ⟨ 1 & 1 & {!!} ⟩
    {!!}

-- induced wild functor
module _ {i₁ i₂ j₁ j₂} {B@(B₀ , _) : Bicat j₁ i₁} {C@(C₀ , _) : Bicat j₂ i₂} where

  private
    instance
      ξB : BicatStr j₁ B₀
      ξB = snd B
      ξC : BicatStr j₂ C₀
      ξC = snd C

  pf-to-wf : Psfunctor {{ξB}} {{ξC}} → Functor-wc (bc-to-wc B) (bc-to-wc C)
  obj (pf-to-wf (psfunctor map-pf ⦃ σ ⦄)) = map-pf
  arr (pf-to-wf (psfunctor map-pf ⦃ σ ⦄)) = F₁ σ
  id (pf-to-wf (psfunctor map-pf ⦃ σ ⦄)) = F-id₁ σ
  comp (pf-to-wf (psfunctor map-pf ⦃ σ ⦄)) = F-◻ σ

  open Nat-trans
  open Pstrans

  ptr-to-ntr : {φ₁ φ₂ : Psfunctor {{ξB}} {{ξC}}} → Pstrans φ₁ φ₂ → Nat-trans (pf-to-wf φ₁) (pf-to-wf φ₂)
  comp (ptr-to-ntr τ) = η₀ τ
  sq (ptr-to-ntr τ) = η₁ τ
