{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.wild-cats.WildCat

-- two fundamental properties of the associator of a wild bicategory

module lib.wild-cats.Bicat where

module _ {i j} {C : WildCat {i} {j}} (trig : triangle-wc C) (pent : pentagon-wc C)
  {a b c : ob C} (g : hom C b c) (f : hom C a b) where

  private

    trig-lamb-aux :
      ap (λ m → ⟦ C ⟧ id₁ C c ▢ m) (ap (λ m → ⟦ C ⟧ m ▢ f) (lamb C g) ∙ ! (α C (id₁ C c) g f)) ◃∎
        =ₛ
      ap (λ m → ⟦ C ⟧ id₁ C c ▢ m) (lamb C (⟦ C ⟧ g ▢ f)) ◃∎
    trig-lamb-aux =
      ap (λ m → ⟦ C ⟧ id₁ C c ▢ m) (ap (λ m → ⟦ C ⟧ m ▢ f) (lamb C g) ∙ ! (α C (id₁ C c) g f)) ◃∎
        =ₛ⟨ ap-∙!◃ (λ m → ⟦ C ⟧ id₁ C c ▢ m) (ap (λ m → ⟦ C ⟧ m ▢ f) (lamb C g)) (α C (id₁ C c) g f) ⟩
      ap (λ m → ⟦ C ⟧ id₁ C c ▢ m) (ap (λ m → ⟦ C ⟧ m ▢ f) (lamb C g)) ◃∙
      ! (ap (λ m → ⟦ C ⟧ id₁ C c ▢ m) (α C (id₁ C c) g f)) ◃∎
        =ₛ₁⟨ 0 & 1 & ∘-ap (λ m → ⟦ C ⟧ id₁ C c ▢ m) (λ m → ⟦ C ⟧ m ▢ f) (lamb C g) ⟩
      ap (λ m → ⟦ C ⟧ id₁ C c ▢ ⟦ C ⟧ m ▢ f) (lamb C g) ◃∙
      ! (ap (λ m → ⟦ C ⟧ id₁ C c ▢ m) (α C (id₁ C c) g f)) ◃∎
        =ₛ⟨ 0 & 1 & hmtpy-nat-∙◃ (λ m → α C (id₁ C c) m f) (lamb C g) ⟩
      α C (id₁ C c) g f ◃∙
      ap (λ m → ⟦ C ⟧ ⟦ C ⟧ id₁ C c ▢ m ▢ f) (lamb C g) ◃∙
      ! (α C (id₁ C c) (⟦ C ⟧ id₁ C c ▢ g) f) ◃∙
      ! (ap (λ m → ⟦ C ⟧ id₁ C c ▢ m) (α C (id₁ C c) g f)) ◃∎
        =ₛ₁⟨ 1 & 1 & ap-∘ (λ m → ⟦ C ⟧ m ▢ f) (λ m → ⟦ C ⟧ id₁ C c ▢ m) (lamb C g) ⟩
      α C (id₁ C c) g f ◃∙
      ap (λ m → ⟦ C ⟧ m ▢ f) (ap (λ m → ⟦ C ⟧ id₁ C c ▢ m) (lamb C g)) ◃∙
      ! (α C (id₁ C c) (⟦ C ⟧ id₁ C c ▢ g) f) ◃∙
      ! (ap (λ m → ⟦ C ⟧ id₁ C c ▢ m) (α C (id₁ C c) g f)) ◃∎
        =ₛ⟨ 1 & 1 & !ₛ (ap-seq-=ₛ (λ m → ⟦ C ⟧ m ▢ f) (triangle-wc◃ {C = C} trig (id₁ C c) g)) ⟩
      α C (id₁ C c) g f ◃∙
      ap (λ m → ⟦ C ⟧ m ▢ f) (ap (λ m → ⟦ C ⟧ m ▢ g) (ρ C (id₁ C c))) ◃∙
      ap (λ m → ⟦ C ⟧ m ▢ f) (! (α C (id₁ C c) (id₁ C c) g)) ◃∙
      ! (α C (id₁ C c) (⟦ C ⟧ id₁ C c ▢ g) f) ◃∙
      ! (ap (λ m → ⟦ C ⟧ id₁ C c ▢ m) (α C (id₁ C c) g f)) ◃∎
        =ₛ⟨ 0 & 1 & apCommSq2◃-rev (λ m → α C m g f) (ρ C (id₁ C c)) ⟩
      ap (λ m → ⟦ C ⟧ m ▢ ⟦ C ⟧ g ▢ f) (ρ C (id₁ C c)) ◃∙
      α C (⟦ C ⟧ id₁ C c ▢ id₁ C c) g f ◃∙
      ! (ap (λ m → ⟦ C ⟧ ⟦ C ⟧ m ▢ g ▢ f) (ρ C (id₁ C c))) ◃∙
      ap (λ m → ⟦ C ⟧ m ▢ f) (ap (λ m → ⟦ C ⟧ m ▢ g) (ρ C (id₁ C c))) ◃∙
      ap (λ m → ⟦ C ⟧ m ▢ f) (! (α C (id₁ C c) (id₁ C c) g)) ◃∙
      ! (α C (id₁ C c) (⟦ C ⟧ id₁ C c ▢ g) f) ◃∙
      ! (ap (λ m → ⟦ C ⟧ id₁ C c ▢ m) (α C (id₁ C c) g f)) ◃∎
        =ₛ⟨ 1 & 1 & !ₛ (pentagon-wc-!-rot1 {C = C} pent (id₁ C c) (id₁ C c) g f) ⟩
      ap (λ m → ⟦ C ⟧ m ▢ ⟦ C ⟧ g ▢ f) (ρ C (id₁ C c)) ◃∙
      ! (α C (id₁ C c) (id₁ C c) (⟦ C ⟧ g ▢ f)) ◃∙
      ap (λ m → ⟦ C ⟧ (id₁ C c) ▢ m) (α C (id₁ C c) g f) ◃∙
      α C (id₁ C c) (⟦ C ⟧ (id₁ C c) ▢ g) f ◃∙
      ap (λ m → ⟦ C ⟧ m ▢ f) (α C (id₁ C c) (id₁ C c) g) ◃∙
      ! (ap (λ m → ⟦ C ⟧ ⟦ C ⟧ m ▢ g ▢ f) (ρ C (id₁ C c))) ◃∙
      ap (λ m → ⟦ C ⟧ m ▢ f) (ap (λ m → ⟦ C ⟧ m ▢ g) (ρ C (id₁ C c))) ◃∙
      ap (λ m → ⟦ C ⟧ m ▢ f) (! (α C (id₁ C c) (id₁ C c) g)) ◃∙
      ! (α C (id₁ C c) (⟦ C ⟧ id₁ C c ▢ g) f) ◃∙
      ! (ap (λ m → ⟦ C ⟧ id₁ C c ▢ m) (α C (id₁ C c) g f)) ◃∎
        =ₛ₁⟨ 6 & 1 & ∘-ap (λ m → ⟦ C ⟧ m ▢ f) (λ m → ⟦ C ⟧ m ▢ g) (ρ C (id₁ C c)) ⟩
      ap (λ m → ⟦ C ⟧ m ▢ ⟦ C ⟧ g ▢ f) (ρ C (id₁ C c)) ◃∙
      ! (α C (id₁ C c) (id₁ C c) (⟦ C ⟧ g ▢ f)) ◃∙
      ap (λ m → ⟦ C ⟧ (id₁ C c) ▢ m) (α C (id₁ C c) g f) ◃∙
      α C (id₁ C c) (⟦ C ⟧ (id₁ C c) ▢ g) f ◃∙
      ap (λ m → ⟦ C ⟧ m ▢ f) (α C (id₁ C c) (id₁ C c) g) ◃∙
      ! (ap (λ m → ⟦ C ⟧ ⟦ C ⟧ m ▢ g ▢ f) (ρ C (id₁ C c))) ◃∙
      ap (λ m → ⟦ C ⟧ ⟦ C ⟧ m ▢ g ▢ f) (ρ C (id₁ C c)) ◃∙
      ap (λ m → ⟦ C ⟧ m ▢ f) (! (α C (id₁ C c) (id₁ C c) g)) ◃∙
      ! (α C (id₁ C c) (⟦ C ⟧ id₁ C c ▢ g) f) ◃∙
      ! (ap (λ m → ⟦ C ⟧ id₁ C c ▢ m) (α C (id₁ C c) g f)) ◃∎
        =ₛ⟨ 5 & 2 & !-inv-l◃ (ap (λ m → ⟦ C ⟧ ⟦ C ⟧ m ▢ g ▢ f) (ρ C (id₁ C c))) ⟩
      ap (λ m → ⟦ C ⟧ m ▢ ⟦ C ⟧ g ▢ f) (ρ C (id₁ C c)) ◃∙
      ! (α C (id₁ C c) (id₁ C c) (⟦ C ⟧ g ▢ f)) ◃∙
      ap (λ m → ⟦ C ⟧ (id₁ C c) ▢ m) (α C (id₁ C c) g f) ◃∙
      α C (id₁ C c) (⟦ C ⟧ (id₁ C c) ▢ g) f ◃∙
      ap (λ m → ⟦ C ⟧ m ▢ f) (α C (id₁ C c) (id₁ C c) g) ◃∙
      ap (λ m → ⟦ C ⟧ m ▢ f) (! (α C (id₁ C c) (id₁ C c) g)) ◃∙
      ! (α C (id₁ C c) (⟦ C ⟧ id₁ C c ▢ g) f) ◃∙
      ! (ap (λ m → ⟦ C ⟧ id₁ C c ▢ m) (α C (id₁ C c) g f)) ◃∎
        =ₛ₁⟨ 5 & 1 & ap-! (λ m → ⟦ C ⟧ m ▢ f) (α C (id₁ C c) (id₁ C c) g) ⟩
      ap (λ m → ⟦ C ⟧ m ▢ ⟦ C ⟧ g ▢ f) (ρ C (id₁ C c)) ◃∙
      ! (α C (id₁ C c) (id₁ C c) (⟦ C ⟧ g ▢ f)) ◃∙
      ap (λ m → ⟦ C ⟧ (id₁ C c) ▢ m) (α C (id₁ C c) g f) ◃∙
      α C (id₁ C c) (⟦ C ⟧ (id₁ C c) ▢ g) f ◃∙
      ap (λ m → ⟦ C ⟧ m ▢ f) (α C (id₁ C c) (id₁ C c) g) ◃∙
      ! (ap (λ m → ⟦ C ⟧ m ▢ f) (α C (id₁ C c) (id₁ C c) g)) ◃∙
      ! (α C (id₁ C c) (⟦ C ⟧ id₁ C c ▢ g) f) ◃∙
      ! (ap (λ m → ⟦ C ⟧ id₁ C c ▢ m) (α C (id₁ C c) g f)) ◃∎
        =ₛ⟨ 4 & 2 & !-inv-r◃ (ap (λ m → ⟦ C ⟧ m ▢ f) (α C (id₁ C c) (id₁ C c) g)) ⟩
      ap (λ m → ⟦ C ⟧ m ▢ ⟦ C ⟧ g ▢ f) (ρ C (id₁ C c)) ◃∙
      ! (α C (id₁ C c) (id₁ C c) (⟦ C ⟧ g ▢ f)) ◃∙
      ap (λ m → ⟦ C ⟧ (id₁ C c) ▢ m) (α C (id₁ C c) g f) ◃∙
      α C (id₁ C c) (⟦ C ⟧ (id₁ C c) ▢ g) f ◃∙
      ! (α C (id₁ C c) (⟦ C ⟧ id₁ C c ▢ g) f) ◃∙
      ! (ap (λ m → ⟦ C ⟧ id₁ C c ▢ m) (α C (id₁ C c) g f)) ◃∎
        =ₛ⟨ 3 & 2 & !-inv-r◃ (α C (id₁ C c) (⟦ C ⟧ id₁ C c ▢ g) f) ⟩
      ap (λ m → ⟦ C ⟧ m ▢ ⟦ C ⟧ g ▢ f) (ρ C (id₁ C c)) ◃∙
      ! (α C (id₁ C c) (id₁ C c) (⟦ C ⟧ g ▢ f)) ◃∙
      ap (λ m → ⟦ C ⟧ (id₁ C c) ▢ m) (α C (id₁ C c) g f) ◃∙
      ! (ap (λ m → ⟦ C ⟧ id₁ C c ▢ m) (α C (id₁ C c) g f)) ◃∎
        =ₛ⟨ 2 & 2 & !-inv-r◃ (ap (λ m → ⟦ C ⟧ id₁ C c ▢ m) (α C (id₁ C c) g f)) ⟩
      ap (λ m → ⟦ C ⟧ m ▢ ⟦ C ⟧ g ▢ f) (ρ C (id₁ C c)) ◃∙
      ! (α C (id₁ C c) (id₁ C c) (⟦ C ⟧ g ▢ f)) ◃∎      
        =ₛ₁⟨ trig (id₁ C c) (⟦ C ⟧ g ▢ f) ⟩
      ap (λ m → ⟦ C ⟧ id₁ C c ▢ m) (lamb C (⟦ C ⟧ g ▢ f)) ◃∎ ∎ₛ

    trig-ρ-aux :
      ap (λ m → ⟦ C ⟧ m ▢ id₁ C a) (ap (λ m → ⟦ C ⟧ g ▢ m) (ρ C f) ∙ α C g f (id₁ C a)) ◃∎
        =ₛ
      ap (λ m → ⟦ C ⟧ m ▢ id₁ C a) (ρ C (⟦ C ⟧ g ▢ f)) ◃∎
    trig-ρ-aux =
      ap (λ m → ⟦ C ⟧ m ▢ id₁ C a) (ap (λ m → ⟦ C ⟧ g ▢ m) (ρ C f) ∙ α C g f (id₁ C a)) ◃∎
        =ₛ⟨ ap-∘-∙◃ (λ m → ⟦ C ⟧ m ▢ id₁ C a) (λ m → ⟦ C ⟧ g ▢ m) (ρ C f) (α C g f (id₁ C a)) ⟩
      ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ▢ m ▢ id₁ C a) (ρ C f) ◃∙
      ap (λ m → ⟦ C ⟧ m ▢ id₁ C a) (α C g f (id₁ C a)) ◃∎
        =ₛ⟨ 0 & 1 & apCommSq◃ (λ m → α C g m (id₁ C a)) (ρ C f) ⟩
      ! (α C g f (id₁ C a)) ◃∙
      ap (λ m → ⟦ C ⟧ g ▢ ⟦ C ⟧ m ▢ id₁ C a) (ρ C f) ◃∙
      α C g (⟦ C ⟧ f ▢ id₁ C a) (id₁ C a) ◃∙
      ap (λ m → ⟦ C ⟧ m ▢ id₁ C a) (α C g f (id₁ C a)) ◃∎
        =ₛ₁⟨ 1 & 1 & ap-∘ (λ m → ⟦ C ⟧ g ▢ m) (λ m → ⟦ C ⟧ m ▢ id₁ C a) (ρ C f) ⟩
      ! (α C g f (id₁ C a)) ◃∙
      ap (λ m → ⟦ C ⟧ g ▢ m) (ap (λ m → ⟦ C ⟧ m ▢ id₁ C a) (ρ C f)) ◃∙
      α C g (⟦ C ⟧ f ▢ id₁ C a) (id₁ C a) ◃∙
      ap (λ m → ⟦ C ⟧ m ▢ id₁ C a) (α C g f (id₁ C a)) ◃∎
        =ₛ⟨ 1 & 1 & ap-seq-=ₛ (λ m → ⟦ C ⟧ g ▢ m) (triangle-wc-rot2 {C = C} trig f (id₁ C a)) ⟩
      ! (α C g f (id₁ C a)) ◃∙
      ap (λ m → ⟦ C ⟧ g ▢ m) (ap (λ m → ⟦ C ⟧ f ▢ m) (lamb C (id₁ C a))) ◃∙
      ap (λ m → ⟦ C ⟧ g ▢ m) (α C f (id₁ C a) (id₁ C a)) ◃∙
      α C g (⟦ C ⟧ f ▢ id₁ C a) (id₁ C a) ◃∙
      ap (λ m → ⟦ C ⟧ m ▢ id₁ C a) (α C g f (id₁ C a)) ◃∎
        =ₛ⟨ 0 & 1 & hmtpy-nat-!◃ (λ m → α C g f m) (lamb C (id₁ C a)) ⟩
      ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ▢ f ▢ m) (lamb C (id₁ C a)) ◃∙
      ! (α C g f (⟦ C ⟧ id₁ C a ▢ id₁ C a)) ◃∙
      ! (ap (λ m → ⟦ C ⟧ g ▢ ⟦ C ⟧ f ▢ m) (lamb C (id₁ C a))) ◃∙
      ap (λ m → ⟦ C ⟧ g ▢ m) (ap (λ m → ⟦ C ⟧ f ▢ m) (lamb C (id₁ C a))) ◃∙
      ap (λ m → ⟦ C ⟧ g ▢ m) (α C f (id₁ C a) (id₁ C a)) ◃∙
      α C g (⟦ C ⟧ f ▢ id₁ C a) (id₁ C a) ◃∙
      ap (λ m → ⟦ C ⟧ m ▢ id₁ C a) (α C g f (id₁ C a)) ◃∎
        =ₛ⟨ 1 & 1 & !ₛ (pentagon-wc-rot4 {C = C} pent g f (id₁ C a) (id₁ C a)) ⟩
      ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ▢ f ▢ m) (lamb C (id₁ C a)) ◃∙
      α C (⟦ C ⟧ g ▢ f) (id₁ C a) (id₁ C a) ◃∙
      ! (ap (λ m → ⟦ C ⟧ m ▢ (id₁ C a)) (α C g f (id₁ C a))) ◃∙
      ! (α C g (⟦ C ⟧ f ▢ (id₁ C a)) (id₁ C a)) ◃∙
      ! (ap (λ m → ⟦ C ⟧ g ▢ m) (α C f (id₁ C a) (id₁ C a))) ◃∙
      ! (ap (λ m → ⟦ C ⟧ g ▢ ⟦ C ⟧ f ▢ m) (lamb C (id₁ C a))) ◃∙
      ap (λ m → ⟦ C ⟧ g ▢ m) (ap (λ m → ⟦ C ⟧ f ▢ m) (lamb C (id₁ C a))) ◃∙
      ap (λ m → ⟦ C ⟧ g ▢ m) (α C f (id₁ C a) (id₁ C a)) ◃∙
      α C g (⟦ C ⟧ f ▢ id₁ C a) (id₁ C a) ◃∙
      ap (λ m → ⟦ C ⟧ m ▢ id₁ C a) (α C g f (id₁ C a)) ◃∎
        =ₛ₁⟨ 6 & 1 & ∘-ap (λ m → ⟦ C ⟧ g ▢ m) (λ m → ⟦ C ⟧ f ▢ m) (lamb C (id₁ C a)) ⟩
      ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ▢ f ▢ m) (lamb C (id₁ C a)) ◃∙
      α C (⟦ C ⟧ g ▢ f) (id₁ C a) (id₁ C a) ◃∙
      ! (ap (λ m → ⟦ C ⟧ m ▢ (id₁ C a)) (α C g f (id₁ C a))) ◃∙
      ! (α C g (⟦ C ⟧ f ▢ (id₁ C a)) (id₁ C a)) ◃∙
      ! (ap (λ m → ⟦ C ⟧ g ▢ m) (α C f (id₁ C a) (id₁ C a))) ◃∙
      ! (ap (λ m → ⟦ C ⟧ g ▢ ⟦ C ⟧ f ▢ m) (lamb C (id₁ C a))) ◃∙
      ap (λ m → ⟦ C ⟧ g ▢ ⟦ C ⟧ f ▢ m) (lamb C (id₁ C a)) ◃∙
      ap (λ m → ⟦ C ⟧ g ▢ m) (α C f (id₁ C a) (id₁ C a)) ◃∙
      α C g (⟦ C ⟧ f ▢ id₁ C a) (id₁ C a) ◃∙
      ap (λ m → ⟦ C ⟧ m ▢ id₁ C a) (α C g f (id₁ C a)) ◃∎
        =ₛ⟨ 5 & 2 & !-inv-l◃ (ap (λ m → ⟦ C ⟧ g ▢ ⟦ C ⟧ f ▢ m) (lamb C (id₁ C a))) ⟩
      ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ▢ f ▢ m) (lamb C (id₁ C a)) ◃∙
      α C (⟦ C ⟧ g ▢ f) (id₁ C a) (id₁ C a) ◃∙
      ! (ap (λ m → ⟦ C ⟧ m ▢ (id₁ C a)) (α C g f (id₁ C a))) ◃∙
      ! (α C g (⟦ C ⟧ f ▢ (id₁ C a)) (id₁ C a)) ◃∙
      ! (ap (λ m → ⟦ C ⟧ g ▢ m) (α C f (id₁ C a) (id₁ C a))) ◃∙
      ap (λ m → ⟦ C ⟧ g ▢ m) (α C f (id₁ C a) (id₁ C a)) ◃∙
      α C g (⟦ C ⟧ f ▢ id₁ C a) (id₁ C a) ◃∙
      ap (λ m → ⟦ C ⟧ m ▢ id₁ C a) (α C g f (id₁ C a)) ◃∎
        =ₛ⟨ 4 & 2 & !-inv-l◃ (ap (λ m → ⟦ C ⟧ g ▢ m) (α C f (id₁ C a) (id₁ C a))) ⟩
      ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ▢ f ▢ m) (lamb C (id₁ C a)) ◃∙
      α C (⟦ C ⟧ g ▢ f) (id₁ C a) (id₁ C a) ◃∙
      ! (ap (λ m → ⟦ C ⟧ m ▢ (id₁ C a)) (α C g f (id₁ C a))) ◃∙
      ! (α C g (⟦ C ⟧ f ▢ (id₁ C a)) (id₁ C a)) ◃∙
      α C g (⟦ C ⟧ f ▢ id₁ C a) (id₁ C a) ◃∙
      ap (λ m → ⟦ C ⟧ m ▢ id₁ C a) (α C g f (id₁ C a)) ◃∎
        =ₛ⟨ 3 & 2 & !-inv-l◃ (α C g (⟦ C ⟧ f ▢ id₁ C a) (id₁ C a)) ⟩
      ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ▢ f ▢ m) (lamb C (id₁ C a)) ◃∙
      α C (⟦ C ⟧ g ▢ f) (id₁ C a) (id₁ C a) ◃∙
      ! (ap (λ m → ⟦ C ⟧ m ▢ (id₁ C a)) (α C g f (id₁ C a))) ◃∙
      ap (λ m → ⟦ C ⟧ m ▢ id₁ C a) (α C g f (id₁ C a)) ◃∎
        =ₛ⟨ 2 & 2 & !-inv-l◃ (ap (λ m → ⟦ C ⟧ m ▢ id₁ C a) (α C g f (id₁ C a))) ⟩
      ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ▢ f ▢ m) (lamb C (id₁ C a)) ◃∙
      α C (⟦ C ⟧ g ▢ f) (id₁ C a) (id₁ C a) ◃∎
        =ₛ⟨ !ₛ (triangle-wc-rot2 {C = C} trig (⟦ C ⟧ g ▢ f) (id₁ C a)) ⟩
      ap (λ m → ⟦ C ⟧ m ▢ id₁ C a) (ρ C (⟦ C ⟧ g ▢ f)) ◃∎ ∎ₛ

  trig-lamb :
    ap (λ m → ⟦ C ⟧ m ▢ f) (lamb C g) ◃∙
    ! (α C (id₁ C c) g f) ◃∎
      =ₛ
    lamb C (⟦ C ⟧ g ▢ f) ◃∎
  trig-lamb = =ₛ-in (id₁-comm-reflect-l {C = C} (=ₛ-out (trig-lamb-aux)))

  trig-lamb-rot1 :
    ap (λ m → ⟦ C ⟧ m ▢ f) (lamb C g) ◃∎
      =ₛ
    lamb C (⟦ C ⟧ g ▢ f) ◃∙
    α C (id₁ C c) g f ◃∎
  trig-lamb-rot1 = post-rotate'-out trig-lamb

  trig-ρ :
    ap (λ m → ⟦ C ⟧ g ▢ m) (ρ C f) ◃∙
    α C g f (id₁ C a) ◃∎
      =ₛ
    ρ C (⟦ C ⟧ g ▢ f) ◃∎
  trig-ρ = =ₛ-in (id₁-comm-reflect-r {C = C} (=ₛ-out (trig-ρ-aux)))

module _ {i j} {C : WildCat {i} {j}} (trig : triangle-wc C) (pent : pentagon-wc C) where

  private
    lamb-ρ-id₁-aux : {a : ob C} → ap (λ m → ⟦ C ⟧ m ▢ id₁ C a) (lamb C (id₁ C a)) ◃∎ =ₛ ap (λ m → ⟦ C ⟧ m ▢ id₁ C a) (ρ C (id₁ C a)) ◃∎
    lamb-ρ-id₁-aux {a} = 
      ap (λ m → ⟦ C ⟧ m ▢ id₁ C a) (lamb C (id₁ C a)) ◃∎
        =ₛ⟨ trig-lamb-rot1 {C = C} trig pent (id₁ C a) (id₁ C a) ⟩
      lamb C (⟦ C ⟧ id₁ C a ▢ id₁ C a) ◃∙
      α C (id₁ C a) (id₁ C a) (id₁ C a) ◃∎
        =ₛ⟨ 0 & 1 & apCommSq2◃ (lamb C) (lamb C (id₁ C a))  ⟩
      ! (ap (λ m → m) (lamb C (id₁ C a))) ◃∙
      lamb C (id₁ C a) ◃∙
      ap (λ m → ⟦ C ⟧ id₁ C a ▢ m) (lamb C (id₁ C a)) ◃∙
      α C (id₁ C a) (id₁ C a) (id₁ C a) ◃∎
        =ₛ₁⟨ 0 & 2 & !-ap-idf-l (lamb C (id₁ C a)) ⟩
      idp ◃∙
      ap (λ m → ⟦ C ⟧ id₁ C a ▢ m) (lamb C (id₁ C a)) ◃∙
      α C (id₁ C a) (id₁ C a) (id₁ C a) ◃∎
        =ₛ₁⟨ ! (=ₛ-out (triangle-wc-rot2 {C = C} trig (id₁ C a) (id₁ C a))) ⟩
      ap (λ m → ⟦ C ⟧ m ▢ id₁ C a) (ρ C (id₁ C a)) ◃∎ ∎ₛ

  lamb-ρ-id₁ : {a : ob C} → lamb C (id₁ C a) == ρ C (id₁ C a)
  lamb-ρ-id₁ {a} = id₁-comm-reflect-r {C = C} (=ₛ-out (lamb-ρ-id₁-aux))
