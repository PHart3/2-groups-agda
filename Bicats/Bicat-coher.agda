{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.wild-cats.WildCat using (triangle-wc; pentagon-wc)
open import lib.wild-cats.Bicat
open import Bicategory
open import Bicat-wild

-- some basic coherence properties of bicategories

module Bicat-coher where

open BicatStr {{...}}


{- We first pass to the underlyhing wild bicategories,
   for which the coherence properties have already been proved. -}
   
module _ {i j} {C₀ : Type i} {{ξC : BicatStr j C₀}} where

  bc-wc-tri : triangle-wc (bc-to-wc (_ , ξC))
  bc-wc-tri {a} {b} g f = =ₛ-out $
    ap (λ m → ⟦ ξC ⟧ m ◻ f) (ρ g) ◃∙
    ! (α g (id₁ b) f) ◃∎
      =ₛ⟨ !ₛ (post-rotate-in (tri-bc◃-rot f g)) ⟩
    ap (λ m → ⟦ ξC ⟧ g ◻ m) (lamb f) ◃∎ ∎ₛ 

  bc-wc-pent : pentagon-wc (bc-to-wc (_ , ξC))
  bc-wc-pent k g h f = =ₛ-out $
    ap (λ m → ⟦ ξC ⟧ m ◻ f) (! (α k g h)) ◃∙
    ! (α k (⟦ ξC ⟧ g ◻ h) f) ◃∙
    ap (λ m → ⟦ ξC ⟧ k ◻ m) (! (α g h f)) ◃∎
      =ₛ₁⟨ 2 & 1 & ap-! (λ m → ⟦ ξC ⟧ k ◻ m) (α g h f) ⟩
    ap (λ m → ⟦ ξC ⟧ m ◻ f) (! (α k g h)) ◃∙
    ! (α k (⟦ ξC ⟧ g ◻ h) f) ◃∙
    ! (ap (λ m → ⟦ ξC ⟧ k ◻ m) (α g h f)) ◃∎
      =ₛ₁⟨ 0 & 1 & ap-! (λ m → ⟦ ξC ⟧ m ◻ f) (α k g h) ⟩
    ! (ap (λ m → ⟦ ξC ⟧ m ◻ f) (α k g h)) ◃∙
    ! (α k (⟦ ξC ⟧ g ◻ h) f) ◃∙
    ! (ap (λ m → ⟦ ξC ⟧ k ◻ m) (α g h f)) ◃∎
      =ₛ⟨ !ₛ (!-=ₛ (pent-bc◃ f h g k)) ⟩
    ! (α (⟦ ξC ⟧ k ◻ g) h f) ◃∙
    ! (α k g (⟦ ξC ⟧ h ◻ f)) ◃∎ ∎ₛ

  module _ {a b c : C₀} (g : hom b c) (f : hom a b) where

    abstract

      trig-lamb-bc :
        ap (λ m → ⟦ ξC ⟧ m ◻ f) (lamb g) ◃∙
        ! (α (id₁ c) g f) ◃∎
          =ₛ
        lamb (⟦ ξC ⟧ g ◻ f) ◃∎
      trig-lamb-bc = trig-lamb {C = bc-to-wc (_ , ξC)} bc-wc-tri bc-wc-pent g f

      trig-lamb-bc-rot :
        ap (λ m → ⟦ ξC ⟧ m ◻ f) (lamb g) ◃∙
        ! (α (id₁ c) g f) ◃∙
        ! (lamb (⟦ ξC ⟧ g ◻ f)) ◃∎
          =ₛ
        []
      trig-lamb-bc-rot = post-rotate'-in trig-lamb-bc

      trig-ρ-bc :
        ap (λ m → ⟦ ξC ⟧ g ◻ m) (ρ f) ◃∙
        α g f (id₁ a) ◃∎
          =ₛ
        ρ (⟦ ξC ⟧ g ◻ f) ◃∎
      trig-ρ-bc =
        ap (λ m → ⟦ ξC ⟧ g ◻ m) (ρ f) ◃∙
        α g f (id₁ a) ◃∎
          =ₛ₁⟨ 1 & 1 & ! (!-! (α g f (id₁ a))) ⟩
        ap (λ m → ⟦ ξC ⟧ g ◻ m) (ρ f) ◃∙
        ! (! (α g f (id₁ a))) ◃∎
          =ₛ⟨ trig-ρ {C = bc-to-wc (_ , ξC)} bc-wc-tri bc-wc-pent g f ⟩
        ρ (⟦ ξC ⟧ g ◻ f) ◃∎ ∎ₛ

      trig-ρ-bc-rot : 
        ρ (⟦ ξC ⟧ g ◻ f) ◃∙
        ! (α g f (id₁ a)) ◃∙
        ap (λ m → ⟦ ξC ⟧ g ◻ m) (! (ρ f)) ◃∎
          =ₛ
        []
      trig-ρ-bc-rot = 
        ρ (⟦ ξC ⟧ g ◻ f) ◃∙
        ! (α g f (id₁ a)) ◃∙
        ap (λ m → ⟦ ξC ⟧ g ◻ m) (! (ρ f)) ◃∎
          =ₛ₁⟨ 2 & 1 & ap-! (λ m → ⟦ ξC ⟧ g ◻ m) (ρ f) ⟩
        ρ (⟦ ξC ⟧ g ◻ f) ◃∙
        ! (α g f (id₁ a)) ◃∙
        ! (ap (λ m → ⟦ ξC ⟧ g ◻ m) (ρ f)) ◃∎
          =ₛ⟨ !ₛ (post-rotate-in (post-rotate-in trig-ρ-bc)) ⟩
        [] ∎ₛ

  abstract

    lamb-ρ-id₁-bc : {a : C₀} → lamb (id₁ a) == ρ (id₁ a)
    lamb-ρ-id₁-bc = lamb-ρ-id₁ {C = bc-to-wc (_ , ξC)} bc-wc-tri bc-wc-pent
