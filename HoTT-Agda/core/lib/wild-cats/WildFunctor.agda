{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.wild-cats.WildCat

module lib.wild-cats.WildFunctor where

record Functor-wc {i₁ j₁ i₂ j₂} (B : WildCat {i₁} {j₁}) (C : WildCat {i₂} {j₂}) :
  Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
  constructor functor-wc
  field
    obj : ob B → ob C
    arr : {a b : ob B} → hom B a b → hom C (obj a) (obj b)
    id : (a : ob B) → arr (id₁ B a) == id₁ C (obj a)
    comp : {a b c : ob B} (f : hom B a b) (g : hom B b c) → arr (⟦ B ⟧ g ▢ f) == ⟦ C ⟧ arr g ▢ arr f
  comp-tri : {a b c d : ob B} (f : hom B a b) (g : hom B b c) (h : hom B c d)
    → arr (⟦ B ⟧ h ▢ ⟦ B ⟧ g ▢ f) == ⟦ C ⟧ arr h ▢ ⟦ C ⟧ arr g ▢ arr f
  comp-tri f g h = comp (⟦ B ⟧ g ▢ f) h ∙ ap (λ m → ⟦ C ⟧ arr h ▢ m) (comp f g)
open Functor-wc public

F-equiv-wc : ∀ {i₁ j₁ i₂ j₂} {B : WildCat {i₁} {j₁}} {C : WildCat {i₂} {j₂}}
  (F : Functor-wc B C) {a b : ob B} {f : hom B a b} → equiv-wc B f → equiv-wc C (arr F f)
fst (F-equiv-wc F {f = f} (g , _)) = arr F g
fst (snd (F-equiv-wc F {a} {f = f} (g , li , _))) = ! (id F a) ∙ ap (arr F) li ∙ comp F f g 
snd (snd (F-equiv-wc F {b = b} {f} (g , _ , ri))) =  ! (id F b) ∙ ap (arr F) ri ∙ comp F g f

module _ {i j} (B : WildCat {i} {j}) where

  idfWC : Functor-wc B B
  obj idfWC = idf (ob B)
  arr idfWC = λ f → f
  id idfWC _ = idp
  comp idfWC _ _ = idp

module _ {i₁ i₂ i₃ j₁ j₂ j₃} {B : WildCat {i₁} {j₁}} {C : WildCat {i₂} {j₂}} {D : WildCat {i₃} {j₃}}  where

  infixr 60 _∘WC_
  _∘WC_ : (φ₂ : Functor-wc C D) (φ₁ : Functor-wc B C) → Functor-wc B D
  obj (φ₂ ∘WC φ₁) = obj φ₂ ∘ obj φ₁
  arr (φ₂ ∘WC φ₁) = arr φ₂ ∘ arr φ₁
  id (φ₂ ∘WC φ₁) x = ap (arr φ₂) (id φ₁ x) ∙ id φ₂ (obj φ₁ x)
  comp (φ₂ ∘WC φ₁) f g = ap (arr φ₂) (comp φ₁ f g) ∙ comp φ₂ (arr φ₁ f) (arr φ₁ g)
