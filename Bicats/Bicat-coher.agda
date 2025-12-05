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
  bc-wc-pent k g h f = =ₛ-out (!ₛ (pent-bc◃ f h g k))
  
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

      trig-lamb-bc-rot2-pre :
        []
          =ₛ
        lamb (⟦ ξC ⟧ g ◻ f) ◃∙
        α (id₁ c) g f ◃∙
        ! (ap (λ m → ⟦ ξC ⟧ m ◻ f) (lamb g)) ◃∎
      trig-lamb-bc-rot2-pre = post-rotate-in (post-rotate'-out trig-lamb-bc)

      trig-lamb-bc-rot2 :
        []
          =ₛ
        lamb (⟦ ξC ⟧ g ◻ f) ◃∙
        α (id₁ c) g f ◃∙
        ap (λ m → ⟦ ξC ⟧ m ◻ f) (! (lamb g)) ◃∎
      trig-lamb-bc-rot2 =
        []
          =ₛ⟨ trig-lamb-bc-rot2-pre ⟩
        lamb (⟦ ξC ⟧ g ◻ f) ◃∙
        α (id₁ c) g f ◃∙
        ! (ap (λ m → ⟦ ξC ⟧ m ◻ f) (lamb g)) ◃∎
          =ₛ₁⟨ 2 & 1 & !-ap (λ m → ⟦ ξC ⟧ m ◻ f) (lamb g) ⟩
        lamb (⟦ ξC ⟧ g ◻ f) ◃∙
        α (id₁ c) g f ◃∙
        ap (λ m → ⟦ ξC ⟧ m ◻ f) (! (lamb g)) ◃∎ ∎ₛ

      trig-lamb-bc-rot3 :
        ! (lamb (⟦ ξC ⟧ g ◻ f)) ◃∙
        ap (λ m → ⟦ ξC ⟧ m ◻ f) (lamb g) ◃∙
        ! (α (id₁ c) g f) ◃∎
          =ₛ
        []
      trig-lamb-bc-rot3 = pre-rotate'-in trig-lamb-bc

      trig-ρ-bc :
        ap (λ m → ⟦ ξC ⟧ g ◻ m) (ρ f) ◃∙
        α g f (id₁ a) ◃∎
          =ₛ
        ρ (⟦ ξC ⟧ g ◻ f) ◃∎
      trig-ρ-bc = trig-ρ {C = bc-to-wc (_ , ξC)} bc-wc-tri bc-wc-pent g f

      trig-ρ-bc-rot-pre :
        ρ (⟦ ξC ⟧ g ◻ f) ◃∙
        ! (α g f (id₁ a)) ◃∙
        ! (ap (λ m → ⟦ ξC ⟧ g ◻ m) (ρ f)) ◃∎
          =ₛ
        []
      trig-ρ-bc-rot-pre = !ₛ (post-rotate-in (post-rotate-in trig-ρ-bc))

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
          =ₛ⟨ trig-ρ-bc-rot-pre ⟩
        [] ∎ₛ

      trig-ρ-bc-rot2 :
        ap (λ m → ⟦ ξC ⟧ g ◻ m) (ρ f) ◃∙
        α g f (id₁ a) ◃∙
        ! (ρ (⟦ ξC ⟧ g ◻ f)) ◃∎
          =ₛ
        []
      trig-ρ-bc-rot2 = post-rotate'-in trig-ρ-bc

  abstract

    lamb-ρ-id₁-bc : {a : C₀} → lamb (id₁ a) == ρ (id₁ a)
    lamb-ρ-id₁-bc = lamb-ρ-id₁ {C = bc-to-wc (_ , ξC)} bc-wc-tri bc-wc-pent

    lamb-ρ-canc : {a : C₀} → lamb (id₁ a) ◃∙ ! (ρ (id₁ a)) ◃∎ =ₛ []
    lamb-ρ-canc {a} = =ₛ-in (ap (λ p → p ∙ ! (ρ (id₁ a))) lamb-ρ-id₁-bc ∙ !-inv-r (ρ (id₁ a)))

    ρ-lamb-id₁2-bc : {a b : C₀} (f : hom a b) → 
      ! (ap (λ m → ⟦ ξC ⟧ m ◻ f) (ρ (⟦ ξC ⟧ id₁ b ◻ id₁ b))) ◃∙
      ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ m ◻ id₁ b ◻ f) (lamb (id₁ b)) ◃∎
        =ₛ
      idp ◃∎
    ρ-lamb-id₁2-bc {a} {b} f = 
      ! (ap (λ m → ⟦ ξC ⟧ m ◻ f) (ρ (⟦ ξC ⟧ id₁ b ◻ id₁ b))) ◃∙
      ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ m ◻ id₁ b ◻ f) (lamb (id₁ b)) ◃∎
        =ₛ⟨ 0 & 1 & apCommSq2◃! (λ v → ap (λ m → ⟦ ξC ⟧ m ◻ f) (ρ v)) (lamb (id₁ b)) ⟩
      ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ m ◻ id₁ b ◻ f) (lamb (id₁ b))) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ m ◻ f) (ρ (id₁ b))) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ f) (lamb (id₁ b)) ◃∙
      ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ m ◻ id₁ b ◻ f) (lamb (id₁ b)) ◃∎
        =ₛ₁⟨ 2 & 1 & ap (ap (λ m → ⟦ ξC ⟧ m ◻ f)) lamb-ρ-id₁-bc ⟩
      ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ m ◻ id₁ b ◻ f) (lamb (id₁ b))) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ m ◻ f) (ρ (id₁ b))) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ f) (ρ (id₁ b)) ◃∙
      ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ m ◻ id₁ b ◻ f) (lamb (id₁ b)) ◃∎
        =ₛ⟨ 1 & 2 & !-inv-l◃ (ap (λ m → ⟦ ξC ⟧ m ◻ f) (ρ (id₁ b))) ⟩
      ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ m ◻ id₁ b ◻ f) (lamb (id₁ b))) ◃∙
      ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ m ◻ id₁ b ◻ f) (lamb (id₁ b)) ◃∎
        =ₛ₁⟨ !-inv-l (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ m ◻ id₁ b ◻ f) (lamb (id₁ b))) ⟩
      idp ◃∎ ∎ₛ

    trig-bc-ρ-λ : {a b : C₀} (f : hom a b) → 
      ! (α f (id₁ a) (id₁ a)) ◃∙
      ρ (⟦ ξC ⟧ f ◻ ⟦ ξC ⟧ id₁ a ◻ id₁ a) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ f ◻ m ◻ id₁ a) (lamb (id₁ a))) ◃∎
        =ₛ
      []
    trig-bc-ρ-λ {a} f =
      ! (α f (id₁ a) (id₁ a)) ◃∙
      ρ (⟦ ξC ⟧ f ◻ ⟦ ξC ⟧ id₁ a ◻ id₁ a) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ f ◻ m ◻ id₁ a) (lamb (id₁ a))) ◃∎
        =ₛ⟨ 0 & 1 & tri-bc◃! (id₁ a) f ⟩
      ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f)) ◃∙
      ap (λ m → ⟦ ξC ⟧ f ◻ m) (lamb (id₁ a)) ◃∙
      ρ (⟦ ξC ⟧ f ◻ ⟦ ξC ⟧ id₁ a ◻ id₁ a) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ f ◻ m ◻ id₁ a) (lamb (id₁ a))) ◃∎
        =ₛ⟨ 2 & 1 & apCommSq2◃ ρ (ρ f ∙ ap (λ m → ⟦ ξC ⟧ f ◻ m) (lamb (id₁ a))) ⟩
      ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f)) ◃∙
      ap (λ m → ⟦ ξC ⟧ f ◻ m) (lamb (id₁ a)) ◃∙
      ! (ap (λ m → m) (ρ f ∙ ap (λ m → ⟦ ξC ⟧ f ◻ m) (lamb (id₁ a)))) ◃∙
      ρ f ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f ∙ ap (λ m → ⟦ ξC ⟧ f ◻ m) (lamb (id₁ a))) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ f ◻ m ◻ id₁ a) (lamb (id₁ a))) ◃∎
        =ₛ₁⟨ 2 & 1 & ap ! (ap-idf (ρ f ∙ ap (λ m → ⟦ ξC ⟧ f ◻ m) (lamb (id₁ a)))) ⟩
      ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f)) ◃∙
      ap (λ m → ⟦ ξC ⟧ f ◻ m) (lamb (id₁ a)) ◃∙
      ! (ρ f ∙ ap (λ m → ⟦ ξC ⟧ f ◻ m) (lamb (id₁ a))) ◃∙
      ρ f ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f ∙ ap (λ m → ⟦ ξC ⟧ f ◻ m) (lamb (id₁ a))) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ f ◻ m ◻ id₁ a) (lamb (id₁ a))) ◃∎
        =ₛ⟨ 2 & 1 & !-∙◃ (ρ f) (ap (λ m → ⟦ ξC ⟧ f ◻ m) (lamb (id₁ a))) ⟩
      ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f)) ◃∙
      ap (λ m → ⟦ ξC ⟧ f ◻ m) (lamb (id₁ a)) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ f ◻ m) (lamb (id₁ a))) ◃∙
      ! (ρ f) ◃∙
      ρ f ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f ∙ ap (λ m → ⟦ ξC ⟧ f ◻ m) (lamb (id₁ a))) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ f ◻ m ◻ id₁ a) (lamb (id₁ a))) ◃∎
        =ₛ⟨ 3 & 2 & !-inv-l◃ (ρ f) ⟩
      ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f)) ◃∙
      ap (λ m → ⟦ ξC ⟧ f ◻ m) (lamb (id₁ a)) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ f ◻ m) (lamb (id₁ a))) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f ∙ ap (λ m → ⟦ ξC ⟧ f ◻ m) (lamb (id₁ a))) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ f ◻ m ◻ id₁ a) (lamb (id₁ a))) ◃∎
        =ₛ⟨ 1 & 2 & !-inv-r◃ (ap (λ m → ⟦ ξC ⟧ f ◻ m) (lamb (id₁ a))) ⟩
      ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f)) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f ∙ ap (λ m → ⟦ ξC ⟧ f ◻ m) (lamb (id₁ a))) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ f ◻ m ◻ id₁ a) (lamb (id₁ a))) ◃∎
        =ₛ⟨ 1 & 1 & ap-∙-∘◃ (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (λ m → ⟦ ξC ⟧ f ◻ m) (ρ f) (lamb (id₁ a)) ⟩
      ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f)) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f) ◃∙
      ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ f ◻ m ◻ id₁ a) (lamb (id₁ a)) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ f ◻ m ◻ id₁ a) (lamb (id₁ a))) ◃∎
        =ₛ⟨ 0 & 2 & !-inv-l◃ (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ a) (ρ f)) ⟩
      ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ f ◻ m ◻ id₁ a) (lamb (id₁ a)) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ f ◻ m ◻ id₁ a) (lamb (id₁ a))) ◃∎
        =ₛ⟨ !-inv-r◃ (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ f ◻ m ◻ id₁ a) (lamb (id₁ a))) ⟩
      [] ∎ₛ
