{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.wild-cats.WildCat
open import lib.wild-cats.WildFunctor
open import lib.wild-cats.WildNatTr

module lib.wild-cats.EquivWC-props where

module _ {ℓc₁ ℓc₂ ℓd₁ ℓd₂ : ULevel} {C : WildCat {ℓc₁} {ℓc₂}} {D : WildCat {ℓd₁} {ℓd₂}} where

  open Nat-trans
  open Equiv-wc
  open HAdjEquiv-wc

  -- Every equivalence of wild categories is a fully faithful functor.
  abstract
    Equiv-wc-ff : (e : Equiv-wc C D) → {x y : ob C} → is-equiv (arr (ftor₁ e) {x} {y})
    Equiv-wc-ff (e@(EquivWC ftor₁ ftor₂ (iso₁-f , iso₁-s) (iso₂-f , iso₂-s))) {x} {y} = let a𝔼@(AEquivWC hae zz) = Equiv-wc-promote e in 
      is-eq (arr ftor₁ {x} {y})
        (λ g → ⟦ C ⟧ <–-wc C (iso₂-s y) ▢ ⟦ C ⟧ arr ftor₂ g ▢ comp iso₂-f x)
        (λ g →
          arr ftor₁ (⟦ C ⟧ <–-wc C (iso₂-s y) ▢ ⟦ C ⟧ arr ftor₂ g ▢ comp iso₂-f x)
            =⟨ comp-tri ftor₁ (comp iso₂-f x) (arr ftor₂ g) (<–-wc C (iso₂-s y)) ⟩
          ⟦ D ⟧ arr ftor₁ (<–-wc C (iso₂-s y)) ▢ ⟦ D ⟧ arr ftor₁ (arr ftor₂ g) ▢ arr ftor₁ (comp iso₂-f x)
            =⟨ ap (λ m → ⟦ D ⟧ m ▢ ⟦ D ⟧ arr ftor₁ (arr ftor₂ g) ▢ arr ftor₁ (comp iso₂-f x)) (zig-zag-eq a𝔼 y) ⟩
          ⟦ D ⟧ comp (fst (iso₁ hae)) (obj ftor₁ y) ▢
          (⟦ D ⟧ arr ftor₁ (arr ftor₂ g) ▢
          arr ftor₁ (comp iso₂-f x))
            =⟨ ! (α D (comp (fst (iso₁ hae)) (obj ftor₁ y)) (arr ftor₁ (arr ftor₂ g)) (arr ftor₁ (comp iso₂-f x))) ⟩
          ⟦ D ⟧ (⟦ D ⟧ comp (fst (iso₁ hae)) (obj ftor₁ y) ▢ arr ftor₁ (arr ftor₂ g)) ▢ arr ftor₁ (comp iso₂-f x)
            =⟨ ap (λ m → ⟦ D ⟧ m ▢ arr ftor₁ (comp iso₂-f x)) (! (sq (fst (iso₁ hae)) g)) ⟩
          ⟦ D ⟧ (⟦ D ⟧ g ▢ comp (fst (iso₁ hae)) (obj ftor₁ x)) ▢ arr ftor₁ (comp iso₂-f x)
            =⟨ α D g (comp (fst (iso₁ hae)) (obj ftor₁ x)) (arr ftor₁ (comp iso₂-f x)) ⟩
          ⟦ D ⟧ g ▢  ⟦ D ⟧ comp (fst (iso₁ hae)) (obj ftor₁ x) ▢ arr ftor₁ (comp iso₂-f x)
            =⟨ ap (λ m → ⟦ D ⟧ g ▢ m) (zig-zag a𝔼 x) ⟩
          ⟦ D ⟧ g ▢ id₁ D (obj ftor₁ x)
            =⟨ ! (ρ D g) ⟩
          g =∎)
        (λ g → 
          ⟦ C ⟧ <–-wc C (iso₂-s y) ▢ ⟦ C ⟧ arr ftor₂ (arr ftor₁ g) ▢ comp iso₂-f x
            =⟨ ap (λ m → ⟦ C ⟧ <–-wc C (iso₂-s y) ▢ m) (sq iso₂-f g) ⟩
          ⟦ C ⟧ <–-wc C (iso₂-s y) ▢ ⟦ C ⟧ comp iso₂-f y ▢ g
            =⟨ ! (α C (<–-wc C (iso₂-s y)) (comp iso₂-f y) g) ⟩
          ⟦ C ⟧ (⟦ C ⟧ <–-wc C (iso₂-s y) ▢  comp iso₂-f y) ▢ g
            =⟨ ap (λ m → ⟦ C ⟧ m ▢ g) (! (<–-wc-linv C (iso₂-s y))) ⟩
          ⟦ C ⟧ id₁ C y ▢ g
            =⟨ ! (lamb C g) ⟩
          g =∎)
