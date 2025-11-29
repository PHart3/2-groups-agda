{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics
open import Bicategory
open import Biadj
open import Pstransf-SIP
open import Psftor-laws
open import Univ-bc
open import Bicat-iso
open import Biequiv
open import Bicat-coher

module Badjbeqv-id where

open BicatStr {{...}}

open Pstrans
open BiequivStr-inst
open Biequiv-coh
open InvMod

-- the identity biadjoint biequivalence
biadj-bieuqiv-id : ∀ {i j} {C₀ : Type i} {{ξC : BicatStr j C₀}} {{uC : is-univ-bc-inst {{ξC}}}} → ξC biadj-bieqv ξC
Ψ-L (fst biadj-bieuqiv-id) = idfBC
Ψ-R (fst biadj-bieuqiv-id) = idfBC
ε (fst biadj-bieuqiv-id) = unitl-ps-≃ idpfBC
η (fst biadj-bieuqiv-id) = unitr-ps-≃ idpfBC
η₀-∼ (ζζ (snd (biadj-bieuqiv-id {{ξC}}))) a = ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb (id₁ a)))
η₁-∼ (ζζ (snd (biadj-bieuqiv-id {{ξC}}))) {a} {b} f = η₁-∼-flip $
  ! (α f (⟦ ξC ⟧ id₁ a ◻ id₁ a) (id₁ a) ∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a)
    (α f (id₁ a) (id₁ a) ∙
    ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ap (λ m → m) (! (ρ f) ∙ lamb f) ∙ idp) ∙
    ! (α (id₁ b) f (id₁ a)) ∙
    ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (! (ρ f) ∙ lamb f) ∙
    α (id₁ b) (id₁ b) f) ∙
  ! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) f (id₁ a)) ∙
  ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ m) (! (ρ f) ∙ lamb f) ∙
  α (⟦ ξC ⟧ id₁ b ◻ id₁ b) (id₁ b) f) ◃∙
  ap (λ m → ⟦ ξC ⟧ f ◻ m) (! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb (id₁ a)))) ◃∙
  (α f (id₁ a) (id₁ a) ∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (! (ρ f) ∙ lamb f) ∙
  ! (α (id₁ b) f (id₁ a)) ∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (! (ρ f) ∙ lamb f) ∙
  α (id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ f) (! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ b) (lamb (id₁ b))))) ◃∎
    =ₑ⟨ 2 & 1 & 
      (α f (id₁ a) (id₁ a) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (! (ρ f) ∙ lamb f) ◃∙
      ! (α (id₁ b) f (id₁ a)) ◃∙
      ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (! (ρ f) ∙ lamb f) ◃∙
      α (id₁ b) (id₁ b) f ◃∎) % =ₛ-in (idp {a =
        α f (id₁ a) (id₁ a) ∙
        ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (! (ρ f) ∙ lamb f) ∙
        ! (α (id₁ b) f (id₁ a)) ∙
        ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (! (ρ f) ∙ lamb f) ∙
        α (id₁ b) (id₁ b) f}) ⟩
  ! (α f (⟦ ξC ⟧ id₁ a ◻ id₁ a) (id₁ a) ∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a)
    (α f (id₁ a) (id₁ a) ∙
    ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ap (λ m → m) (! (ρ f) ∙ lamb f) ∙ idp) ∙
    ! (α (id₁ b) f (id₁ a)) ∙
    ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (! (ρ f) ∙ lamb f) ∙
    α (id₁ b) (id₁ b) f) ∙
  ! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) f (id₁ a)) ∙
  ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ m) (! (ρ f) ∙ lamb f) ∙
  α (⟦ ξC ⟧ id₁ b ◻ id₁ b) (id₁ b) f) ◃∙
  ap (λ m → ⟦ ξC ⟧ f ◻ m) (! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb (id₁ a)))) ◃∙
  α f (id₁ a) (id₁ a) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (! (ρ f) ∙ lamb f) ◃∙
  ! (α (id₁ b) f (id₁ a)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (! (ρ f) ∙ lamb f) ◃∙
  α (id₁ b) (id₁ b) f ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ f) (! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ b) (lamb (id₁ b))))) ◃∎
    =ₛ⟨ 0 & 1 & !-∙-seq
      (α f (⟦ ξC ⟧ id₁ a ◻ id₁ a) (id₁ a) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a)
        (α f (id₁ a) (id₁ a) ∙
        ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ap (λ m → m) (! (ρ f) ∙ lamb f) ∙ idp) ∙
        ! (α (id₁ b) f (id₁ a)) ∙
        ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (! (ρ f) ∙ lamb f) ∙
        α (id₁ b) (id₁ b) f) ◃∙
      ! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) f (id₁ a)) ◃∙
      ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ m) (! (ρ f) ∙ lamb f) ◃∙
      α (⟦ ξC ⟧ id₁ b ◻ id₁ b) (id₁ b) f ◃∎) ⟩
  ! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ m) (! (ρ f) ∙ lamb f)) ◃∙
  ! (! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) f (id₁ a))) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a)
      (α f (id₁ a) (id₁ a) ∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ap (λ m → m) (! (ρ f) ∙ lamb f) ∙ idp) ∙
      ! (α (id₁ b) f (id₁ a)) ∙
      ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (! (ρ f) ∙ lamb f) ∙
      α (id₁ b) (id₁ b) f)) ◃∙
  ! (α f (⟦ ξC ⟧ id₁ a ◻ id₁ a) (id₁ a)) ◃∙
  ap (λ m → ⟦ ξC ⟧ f ◻ m) (! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb (id₁ a)))) ◃∙
  α f (id₁ a) (id₁ a) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (! (ρ f) ∙ lamb f) ◃∙
  ! (α (id₁ b) f (id₁ a)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (! (ρ f) ∙ lamb f) ◃∙
  α (id₁ b) (id₁ b) f ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ f) (! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ b) (lamb (id₁ b))))) ◃∎
    =ₛ⟨ 3 & 1 & apCommSq◃! ρ
      (α f (id₁ a) (id₁ a) ∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ap (λ m → m) (! (ρ f) ∙ lamb f) ∙ idp) ∙
      ! (α (id₁ b) f (id₁ a)) ∙
      ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (! (ρ f) ∙ lamb f) ∙
      α (id₁ b) (id₁ b) f) ⟩
  ! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ m) (! (ρ f) ∙ lamb f)) ◃∙
  ! (! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) f (id₁ a))) ◃∙
  ! (ρ (⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ f)) ◃∙
  ! (ap (λ m → m)
      (α f (id₁ a) (id₁ a) ∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ap (λ m → m) (! (ρ f) ∙ lamb f) ∙ idp) ∙
      ! (α (id₁ b) f (id₁ a)) ∙
      ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (! (ρ f) ∙ lamb f) ∙
      α (id₁ b) (id₁ b) f)) ◃∙
  ρ (⟦ ξC ⟧ f ◻ ⟦ ξC ⟧ id₁ a ◻ id₁ a) ◃∙
  ! (α f (⟦ ξC ⟧ id₁ a ◻ id₁ a) (id₁ a)) ◃∙
  ap (λ m → ⟦ ξC ⟧ f ◻ m) (! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb (id₁ a)))) ◃∙
  α f (id₁ a) (id₁ a) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (! (ρ f) ∙ lamb f) ◃∙
  ! (α (id₁ b) f (id₁ a)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (! (ρ f) ∙ lamb f) ◃∙
  α (id₁ b) (id₁ b) f ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ f) (! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ b) (lamb (id₁ b))))) ◃∎
    =ₛ₁⟨ 4 & 1 & ap ! (ap-idf
      (α f (id₁ a) (id₁ a) ∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ap (λ m → m) (! (ρ f) ∙ lamb f) ∙ idp) ∙
      ! (α (id₁ b) f (id₁ a)) ∙
      ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (! (ρ f) ∙ lamb f) ∙
      α (id₁ b) (id₁ b) f)) ⟩
  ! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ m) (! (ρ f) ∙ lamb f)) ◃∙
  ! (! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) f (id₁ a))) ◃∙
  ! (ρ (⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ f)) ◃∙
  ! (α f (id₁ a) (id₁ a) ∙
    ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ap (λ m → m) (! (ρ f) ∙ lamb f) ∙ idp) ∙
    ! (α (id₁ b) f (id₁ a)) ∙
    ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (! (ρ f) ∙ lamb f) ∙
    α (id₁ b) (id₁ b) f) ◃∙
  ρ (⟦ ξC ⟧ f ◻ ⟦ ξC ⟧ id₁ a ◻ id₁ a) ◃∙
  ! (α f (⟦ ξC ⟧ id₁ a ◻ id₁ a) (id₁ a)) ◃∙
  ap (λ m → ⟦ ξC ⟧ f ◻ m) (! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb (id₁ a)))) ◃∙
  α f (id₁ a) (id₁ a) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (! (ρ f) ∙ lamb f) ◃∙
  ! (α (id₁ b) f (id₁ a)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (! (ρ f) ∙ lamb f) ◃∙
  α (id₁ b) (id₁ b) f ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ f) (! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ b) (lamb (id₁ b))))) ◃∎
    =ₛ⟨ 4 & 1 & !-∙-seq
      (α f (id₁ a) (id₁ a) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ap (λ m → m) (! (ρ f) ∙ lamb f) ∙ idp) ◃∙
      ! (α (id₁ b) f (id₁ a)) ◃∙
      ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (! (ρ f) ∙ lamb f) ◃∙
      α (id₁ b) (id₁ b) f ◃∎) ⟩
  ! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ m) (! (ρ f) ∙ lamb f)) ◃∙
  ! (! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) f (id₁ a))) ◃∙
  ! (ρ (⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ f)) ◃∙
  ! (α (id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (! (ρ f) ∙ lamb f)) ◃∙
  ! (! (α (id₁ b) f (id₁ a))) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ap (λ m → m) (! (ρ f) ∙ lamb f) ∙ idp)) ◃∙
  ! (α f (id₁ a) (id₁ a)) ◃∙
  ρ (⟦ ξC ⟧ f ◻ ⟦ ξC ⟧ id₁ a ◻ id₁ a) ◃∙
  ! (α f (⟦ ξC ⟧ id₁ a ◻ id₁ a) (id₁ a)) ◃∙
  ap (λ m → ⟦ ξC ⟧ f ◻ m) (! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb (id₁ a)))) ◃∙
  α f (id₁ a) (id₁ a) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (! (ρ f) ∙ lamb f) ◃∙
  ! (α (id₁ b) f (id₁ a)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (! (ρ f) ∙ lamb f) ◃∙
  α (id₁ b) (id₁ b) f ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ f) (! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ b) (lamb (id₁ b))))) ◃∎
    =ₛ⟨ 7 & 1 & !-ap-idf-!-∙-unit-r (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f) (lamb f) ⟩
  ! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ m) (! (ρ f) ∙ lamb f)) ◃∙
  ! (! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) f (id₁ a))) ◃∙
  ! (ρ (⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ f)) ◃∙
  ! (α (id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (! (ρ f) ∙ lamb f)) ◃∙
  ! (! (α (id₁ b) f (id₁ a))) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f) ◃∙
  ! (α f (id₁ a) (id₁ a)) ◃∙
  ρ (⟦ ξC ⟧ f ◻ ⟦ ξC ⟧ id₁ a ◻ id₁ a) ◃∙
  ! (α f (⟦ ξC ⟧ id₁ a ◻ id₁ a) (id₁ a)) ◃∙
  ap (λ m → ⟦ ξC ⟧ f ◻ m) (! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb (id₁ a)))) ◃∙
  α f (id₁ a) (id₁ a) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (! (ρ f) ∙ lamb f) ◃∙
  ! (α (id₁ b) f (id₁ a)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (! (ρ f) ∙ lamb f) ◃∙
  α (id₁ b) (id₁ b) f ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ f) (! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ b) (lamb (id₁ b))))) ◃∎
    =ₛ₁⟨ 2 & 1 & !-! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) f (id₁ a)) ⟩
  ! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ m) (! (ρ f) ∙ lamb f)) ◃∙
  α (⟦ ξC ⟧ id₁ b ◻ id₁ b) f (id₁ a) ◃∙
  ! (ρ (⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ f)) ◃∙
  ! (α (id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (! (ρ f) ∙ lamb f)) ◃∙
  ! (! (α (id₁ b) f (id₁ a))) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f) ◃∙
  ! (α f (id₁ a) (id₁ a)) ◃∙
  ρ (⟦ ξC ⟧ f ◻ ⟦ ξC ⟧ id₁ a ◻ id₁ a) ◃∙
  ! (α f (⟦ ξC ⟧ id₁ a ◻ id₁ a) (id₁ a)) ◃∙
  ap (λ m → ⟦ ξC ⟧ f ◻ m) (! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb (id₁ a)))) ◃∙
  α f (id₁ a) (id₁ a) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (! (ρ f) ∙ lamb f) ◃∙
  ! (α (id₁ b) f (id₁ a)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (! (ρ f) ∙ lamb f) ◃∙
  α (id₁ b) (id₁ b) f ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ f) (! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ b) (lamb (id₁ b))))) ◃∎
    =ₛ⟨ 5 & 1 & !-ap-!∙◃ (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (ρ f) (lamb f) ⟩
  ! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ m) (! (ρ f) ∙ lamb f)) ◃∙
  α (⟦ ξC ⟧ id₁ b ◻ id₁ b) f (id₁ a) ◃∙
  ! (ρ (⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ f)) ◃∙
  ! (α (id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (ρ f) ◃∙
  ! (! (α (id₁ b) f (id₁ a))) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f) ◃∙
  ! (α f (id₁ a) (id₁ a)) ◃∙
  ρ (⟦ ξC ⟧ f ◻ ⟦ ξC ⟧ id₁ a ◻ id₁ a) ◃∙
  ! (α f (⟦ ξC ⟧ id₁ a ◻ id₁ a) (id₁ a)) ◃∙
  ap (λ m → ⟦ ξC ⟧ f ◻ m) (! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb (id₁ a)))) ◃∙
  α f (id₁ a) (id₁ a) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (! (ρ f) ∙ lamb f) ◃∙
  ! (α (id₁ b) f (id₁ a)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (! (ρ f) ∙ lamb f) ◃∙
  α (id₁ b) (id₁ b) f ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ f) (! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ b) (lamb (id₁ b))))) ◃∎
    =ₛ₁⟨ 7 & 1 & !-! (α (id₁ b) f (id₁ a)) ⟩
  ! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ m) (! (ρ f) ∙ lamb f)) ◃∙
  α (⟦ ξC ⟧ id₁ b ◻ id₁ b) f (id₁ a) ◃∙
  ! (ρ (⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ f)) ◃∙
  ! (α (id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (ρ f) ◃∙
  α (id₁ b) f (id₁ a) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f) ◃∙
  ! (α f (id₁ a) (id₁ a)) ◃∙
  ρ (⟦ ξC ⟧ f ◻ ⟦ ξC ⟧ id₁ a ◻ id₁ a) ◃∙
  ! (α f (⟦ ξC ⟧ id₁ a ◻ id₁ a) (id₁ a)) ◃∙
  ap (λ m → ⟦ ξC ⟧ f ◻ m) (! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb (id₁ a)))) ◃∙
  α f (id₁ a) (id₁ a) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (! (ρ f) ∙ lamb f) ◃∙
  ! (α (id₁ b) f (id₁ a)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (! (ρ f) ∙ lamb f) ◃∙
  α (id₁ b) (id₁ b) f ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ f) (! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ b) (lamb (id₁ b))))) ◃∎
    =ₛ₁⟨ 13 & 1 & !-∘-ap (λ m → ⟦ ξC ⟧ f ◻ m) (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb (id₁ a)) ⟩
  ! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ m) (! (ρ f) ∙ lamb f)) ◃∙
  α (⟦ ξC ⟧ id₁ b ◻ id₁ b) f (id₁ a) ◃∙
  ! (ρ (⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ f)) ◃∙
  ! (α (id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (ρ f) ◃∙
  α (id₁ b) f (id₁ a) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f) ◃∙
  ! (α f (id₁ a) (id₁ a)) ◃∙
  ρ (⟦ ξC ⟧ f ◻ ⟦ ξC ⟧ id₁ a ◻ id₁ a) ◃∙
  ! (α f (⟦ ξC ⟧ id₁ a ◻ id₁ a) (id₁ a)) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ f ◻ ⟦ ξC ⟧ m ◻ id₁ a) (lamb (id₁ a))) ◃∙
  α f (id₁ a) (id₁ a) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (! (ρ f) ∙ lamb f) ◃∙
  ! (α (id₁ b) f (id₁ a)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (! (ρ f) ∙ lamb f) ◃∙
  α (id₁ b) (id₁ b) f ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ f) (! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ b) (lamb (id₁ b))))) ◃∎
    =ₛ₁⟨ 19 & 1 & ∘-!-ap-! (λ m → ⟦ ξC ⟧ m ◻ f) (λ m → ⟦ ξC ⟧ m ◻ id₁ b) (lamb (id₁ b)) ⟩
  ! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ m) (! (ρ f) ∙ lamb f)) ◃∙
  α (⟦ ξC ⟧ id₁ b ◻ id₁ b) f (id₁ a) ◃∙
  ! (ρ (⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ f)) ◃∙
  ! (α (id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (ρ f) ◃∙
  α (id₁ b) f (id₁ a) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f) ◃∙
  ! (α f (id₁ a) (id₁ a)) ◃∙
  ρ (⟦ ξC ⟧ f ◻ ⟦ ξC ⟧ id₁ a ◻ id₁ a) ◃∙
  ! (α f (⟦ ξC ⟧ id₁ a ◻ id₁ a) (id₁ a)) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ f ◻ ⟦ ξC ⟧ m ◻ id₁ a) (lamb (id₁ a))) ◃∙
  α f (id₁ a) (id₁ a) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (! (ρ f) ∙ lamb f) ◃∙
  ! (α (id₁ b) f (id₁ a)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (! (ρ f) ∙ lamb f) ◃∙
  α (id₁ b) (id₁ b) f ◃∙
  ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ m ◻ id₁ b ◻ f) (lamb (id₁ b)) ◃∎
    =ₛ⟨ 17 & 1 & ap-!∙◃ (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (ρ f) (lamb f) ⟩
  ! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ m) (! (ρ f) ∙ lamb f)) ◃∙
  α (⟦ ξC ⟧ id₁ b ◻ id₁ b) f (id₁ a) ◃∙
  ! (ρ (⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ f)) ◃∙
  ! (α (id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (ρ f) ◃∙
  α (id₁ b) f (id₁ a) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f) ◃∙
  ! (α f (id₁ a) (id₁ a)) ◃∙
  ρ (⟦ ξC ⟧ f ◻ ⟦ ξC ⟧ id₁ a ◻ id₁ a) ◃∙
  ! (α f (⟦ ξC ⟧ id₁ a ◻ id₁ a) (id₁ a)) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ f ◻ ⟦ ξC ⟧ m ◻ id₁ a) (lamb (id₁ a))) ◃∙
  α f (id₁ a) (id₁ a) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (! (ρ f) ∙ lamb f) ◃∙
  ! (α (id₁ b) f (id₁ a)) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (ρ f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (lamb f) ◃∙
  α (id₁ b) (id₁ b) f ◃∙
  ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ m ◻ id₁ b ◻ f) (lamb (id₁ b)) ◃∎
    =ₛ⟨ 15 & 1 & ap-!∙◃ (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f) (lamb f) ⟩
  ! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ m) (! (ρ f) ∙ lamb f)) ◃∙
  α (⟦ ξC ⟧ id₁ b ◻ id₁ b) f (id₁ a) ◃∙
  ! (ρ (⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ f)) ◃∙
  ! (α (id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (ρ f) ◃∙
  α (id₁ b) f (id₁ a) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f) ◃∙
  ! (α f (id₁ a) (id₁ a)) ◃∙
  ρ (⟦ ξC ⟧ f ◻ ⟦ ξC ⟧ id₁ a ◻ id₁ a) ◃∙
  ! (α f (⟦ ξC ⟧ id₁ a ◻ id₁ a) (id₁ a)) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ f ◻ ⟦ ξC ⟧ m ◻ id₁ a) (lamb (id₁ a))) ◃∙
  α f (id₁ a) (id₁ a) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb f) ◃∙
  ! (α (id₁ b) f (id₁ a)) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (ρ f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (lamb f) ◃∙
  α (id₁ b) (id₁ b) f ◃∙
  ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ m ◻ id₁ b ◻ f) (lamb (id₁ b)) ◃∎
    =ₛ⟨ 1 & 1 & !-ap-!∙◃ (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ m) (ρ f) (lamb f) ⟩
  ! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ m) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ m) (ρ f) ◃∙
  α (⟦ ξC ⟧ id₁ b ◻ id₁ b) f (id₁ a) ◃∙
  ! (ρ (⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ f)) ◃∙
  ! (α (id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (ρ f) ◃∙
  α (id₁ b) f (id₁ a) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f) ◃∙
  ! (α f (id₁ a) (id₁ a)) ◃∙
  ρ (⟦ ξC ⟧ f ◻ ⟦ ξC ⟧ id₁ a ◻ id₁ a) ◃∙
  ! (α f (⟦ ξC ⟧ id₁ a ◻ id₁ a) (id₁ a)) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ f ◻ ⟦ ξC ⟧ m ◻ id₁ a) (lamb (id₁ a))) ◃∙
  α f (id₁ a) (id₁ a) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb f) ◃∙
  ! (α (id₁ b) f (id₁ a)) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (ρ f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (lamb f) ◃∙
  α (id₁ b) (id₁ b) f ◃∙
  ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ m ◻ id₁ b ◻ f) (lamb (id₁ b)) ◃∎
    =ₛ⟨ 2 & 3 & trig-ρ-bc-rot2 (⟦ ξC ⟧ id₁ b ◻ id₁ b) f ⟩
  ! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ m) (lamb f)) ◃∙
  ! (α (id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (ρ f) ◃∙
  α (id₁ b) f (id₁ a) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f) ◃∙
  ! (α f (id₁ a) (id₁ a)) ◃∙
  ρ (⟦ ξC ⟧ f ◻ ⟦ ξC ⟧ id₁ a ◻ id₁ a) ◃∙
  ! (α f (⟦ ξC ⟧ id₁ a ◻ id₁ a) (id₁ a)) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ f ◻ ⟦ ξC ⟧ m ◻ id₁ a) (lamb (id₁ a))) ◃∙
  α f (id₁ a) (id₁ a) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb f) ◃∙
  ! (α (id₁ b) f (id₁ a)) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (ρ f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (lamb f) ◃∙
  α (id₁ b) (id₁ b) f ◃∙
  ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ m ◻ id₁ b ◻ f) (lamb (id₁ b)) ◃∎
    =ₛ⟨ 10 & 3 & !ₛ (apCommSq◃! (λ m → α f m (id₁ a))  (lamb (id₁ a))) ⟩
  ! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ m) (lamb f)) ◃∙
  ! (α (id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (ρ f) ◃∙
  α (id₁ b) f (id₁ a) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f) ◃∙
  ! (α f (id₁ a) (id₁ a)) ◃∙
  ρ (⟦ ξC ⟧ f ◻ ⟦ ξC ⟧ id₁ a ◻ id₁ a) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ f ◻ m ◻ id₁ a) (lamb (id₁ a))) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb f) ◃∙
  ! (α (id₁ b) f (id₁ a)) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (ρ f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (lamb f) ◃∙
  α (id₁ b) (id₁ b) f ◃∙
  ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ m ◻ id₁ b ◻ f) (lamb (id₁ b)) ◃∎
    =ₛ⟨ 8 & 3 & trig-bc-ρ-λ f ⟩
  ! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ m) (lamb f)) ◃∙
  ! (α (id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (ρ f) ◃∙
  α (id₁ b) f (id₁ a) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb f) ◃∙
  ! (α (id₁ b) f (id₁ a)) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (ρ f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (lamb f) ◃∙
  α (id₁ b) (id₁ b) f ◃∙
  ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ m ◻ id₁ b ◻ f) (lamb (id₁ b)) ◃∎
    =ₛ⟨ 7 & 2 & !-inv-r◃ (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f)) ⟩
  ! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ m) (lamb f)) ◃∙
  ! (α (id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (ρ f) ◃∙
  α (id₁ b) f (id₁ a) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb f) ◃∙
  ! (α (id₁ b) f (id₁ a)) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (ρ f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (lamb f) ◃∙
  α (id₁ b) (id₁ b) f ◃∙
  ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ m ◻ id₁ b ◻ f) (lamb (id₁ b)) ◃∎
    =ₛ⟨ 6 & 2 & !-inv-l◃ (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (lamb f)) ⟩
  ! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ m) (lamb f)) ◃∙
  ! (α (id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (ρ f) ◃∙
  α (id₁ b) f (id₁ a) ◃∙
  ! (α (id₁ b) f (id₁ a)) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (ρ f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (lamb f) ◃∙
  α (id₁ b) (id₁ b) f ◃∙
  ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ m ◻ id₁ b ◻ f) (lamb (id₁ b)) ◃∎
    =ₛ⟨ 5 & 2 & !-inv-r◃ (α (id₁ b) f (id₁ a)) ⟩
  ! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ m) (lamb f)) ◃∙
  ! (α (id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (ρ f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (ρ f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (lamb f) ◃∙
  α (id₁ b) (id₁ b) f ◃∙
  ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ m ◻ id₁ b ◻ f) (lamb (id₁ b)) ◃∎
    =ₛ⟨ 4 & 2 & !-inv-r◃ (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (ρ f))  ⟩
  ! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ m) (lamb f)) ◃∙
  ! (α (id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (lamb f) ◃∙
  α (id₁ b) (id₁ b) f ◃∙
  ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ m ◻ id₁ b ◻ f) (lamb (id₁ b)) ◃∎
    =ₛ⟨ 3 & 2 & !-inv-l◃ (ap (λ m → ⟦ ξC ⟧ id₁ b ◻ m) (lamb f)) ⟩
  ! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ m) (lamb f)) ◃∙
  ! (α (id₁ b) (id₁ b) f) ◃∙
  α (id₁ b) (id₁ b) f ◃∙
  ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ m ◻ id₁ b ◻ f) (lamb (id₁ b)) ◃∎
    =ₛ⟨ 2 & 2 & !-inv-l◃ (α (id₁ b) (id₁ b) f) ⟩
  ! (α (⟦ ξC ⟧ id₁ b ◻ id₁ b) (id₁ b) f) ◃∙
  ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ id₁ b ◻ id₁ b ◻ m) (lamb f)) ◃∙
  ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ m ◻ id₁ b ◻ f) (lamb (id₁ b)) ◃∎
    =ₛ⟨ 0 & 2 & !ₛ (tri-bc◃-rot4 f (⟦ ξC ⟧ id₁ b ◻ id₁ b)) ⟩
  ! (ap (λ m → ⟦ ξC ⟧ m ◻ f) (ρ (⟦ ξC ⟧ id₁ b ◻ id₁ b))) ◃∙
  ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ m ◻ id₁ b ◻ f) (lamb (id₁ b)) ◃∎
    =ₛ⟨ ρ-lamb-id₁2-bc f ⟩
  idp ◃∎ ∎ₛ
