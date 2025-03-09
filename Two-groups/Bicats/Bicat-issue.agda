{-# OPTIONS --without-K #-}

module Bicat-issue where

open import Agda.Primitive renaming (_⊔_ to lmax; lsuc to lsucc)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)

module _ (j : Level) where

  record PreMagStr {i} (B₀ : Set i) : Set (lmax i (lsucc j)) where
    infixr 82 _◻_
    field
      hom : B₀ → B₀ → Set j
      _◻_ : {a b c : B₀} → hom b c → hom a b → hom a c

open PreMagStr {{...}}

module _ {i₁ i₂ j₁ j₂} {B₀ : Set i₁} {C₀ : Set i₂} {{ξB : PreMagStr j₁ B₀}} {{ξC : PreMagStr j₂ C₀}} where

  record FunctorStr (F₀ : B₀ → C₀) : Set (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
    field
      F₁ : {a b : B₀} → hom a b → hom (F₀ a) (F₀ b)
      F-◻ : {a b c : B₀} (f : hom a b) (g : hom b c) → F₁ (g ◻ f) == F₁ g ◻ F₁ f
{-

———— Errors ————————————————————————————————————————————————
Failed to solve the following constraints:
  Is usable at default modality: (F₁
                                  : {a b : B₀} →
                                    PreMagStr.hom ξB a b → PreMagStr.hom ξC (F₀ a) (F₀ b))
                                 (F-◻
                                  : {a b c : B₀} (f : PreMagStr.hom ξB a b)
                                    (g : PreMagStr.hom ξB b c) →
                                    F₁ ((_r_53 (F₀ = F₀) (F₁ = F₁) (f = f) (g = g) PreMagStr.◻ g) f)
                                    ==
                                    (_r_66 (F₀ = F₀) (F₁ = F₁) (f = f) (g = g) PreMagStr.◻ F₁ g)
                                    (F₁ f)) →
                                 FunctorStr F₀
    (blocked on _a_48)
  Resolve instance argument _r_53 : PreMagStr _j_50 _B₀_52
  Candidates
    ξC : PreMagStr j₂ C₀
    ξB : PreMagStr j₁ B₀
    (stuck)
  Resolve instance argument _r_66 : PreMagStr _j_63 _B₀_65
  Candidates
    ξC : PreMagStr j₂ C₀
    ξB : PreMagStr j₁ B₀
    (stuck)
  PreMagStr.hom _r_66 _a_67 _c_69
    =< PreMagStr.hom ξC (F₀ _a_48) (F₀ _b_49)
    (blocked on _r_66)
  PreMagStr.hom ξC (F₀ a) (F₀ b) =< PreMagStr.hom _r_66 _a_67 _b_68
    (blocked on _r_66)
  PreMagStr.hom ξC (F₀ b) (F₀ c) =< PreMagStr.hom _r_66 _b_68 _c_69
    (blocked on _r_66)
  PreMagStr.hom _r_53 _a_54 _c_56 =< PreMagStr.hom ξB _a_48 _b_49
    (blocked on _r_53)
  PreMagStr.hom ξB a b =< PreMagStr.hom _r_53 _a_54 _b_55
    (blocked on _r_53)
  PreMagStr.hom ξB b c =< PreMagStr.hom _r_53 _b_55 _c_56
    (blocked on _r_53)

-}
