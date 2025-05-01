{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Sigma

module lib.wild-cats.WildCat where

record WildCat {i j} : Type (lmax (lsucc i) (lsucc j)) where
  constructor wildcat
  infixr 82 _▢_
  field
    ob : Type i
    hom : ob → ob → Type j
    id₁ : (a : ob) → hom a a
    _▢_ : {a b c : ob} → hom b c → hom a b → hom a c
    ρ : {a b : ob} (f : hom a b) → f == f ▢ id₁ a
    lamb : {a b : ob} (f : hom a b) → f == id₁ b ▢ f
    α : {a b c d : ob} (h : hom c d) (g : hom b c) (f : hom a b) → (h ▢ g) ▢ f == h ▢ g ▢ f
open WildCat public

infixr 82 ⟦_⟧_▢_
⟦_⟧_▢_ : ∀ {i j} (C : WildCat {i} {j}) {a b c : ob C} → hom C b c → hom C a b → hom C a c
⟦_⟧_▢_ ξ g f = _▢_ ξ g f 

module _ {i j} (C : WildCat {i} {j}) where

  equiv-wc : {a b : ob C} → hom C a b → Type j
  equiv-wc {a} {b} f = Σ (hom C b a) (λ g → (id₁ C a == ⟦ C ⟧ g ▢ f) × (id₁ C b == ⟦ C ⟧ f ▢ g))  

  module _ {a b : ob C} {f : hom C a b} (e : equiv-wc f) where

    <–-wc : hom C b a
    <–-wc = fst e

    <–-wc-linv : id₁ C a == ⟦ C ⟧ <–-wc ▢ f
    <–-wc-linv = fst (snd e)

    <–-wc-rinv : id₁ C b == ⟦ C ⟧ f ▢ <–-wc
    <–-wc-rinv = snd (snd e)

    equiv-wc-rev : equiv-wc <–-wc
    fst equiv-wc-rev = f
    fst (snd equiv-wc-rev) = <–-wc-rinv
    snd (snd equiv-wc-rev) = <–-wc-linv

  equiv-wc-∘ : {a b c : ob C} {f : hom C a b} {g : hom C b c}
    → equiv-wc g → equiv-wc f → equiv-wc (⟦ C ⟧ g ▢ f)
  fst (equiv-wc-∘ eg ef) = ⟦ C ⟧ <–-wc ef ▢ <–-wc eg
  fst (snd (equiv-wc-∘ {f = f} {g} eg ef)) =
    <–-wc-linv ef ∙
    ap (λ m → ⟦ C ⟧ <–-wc ef ▢  m) (lamb C f) ∙
    ap (λ m → ⟦ C ⟧ <–-wc ef ▢  ⟦ C ⟧ m ▢ f) (<–-wc-linv eg) ∙
    ap (λ m → ⟦ C ⟧ <–-wc ef ▢ m) (α C (<–-wc eg) g f) ∙
    ! (α C (<–-wc ef) (<–-wc eg) (⟦ C ⟧ g ▢ f))
  snd (snd (equiv-wc-∘ {f = f} {g} eg ef)) = 
    <–-wc-rinv eg ∙
    ap (λ m → ⟦ C ⟧ m ▢  <–-wc eg) (ρ C g) ∙
    ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ▢  m ▢ <–-wc eg) (<–-wc-rinv ef) ∙
    α C g (⟦ C ⟧ f ▢ <–-wc ef) (<–-wc eg) ∙
    ap (λ m → ⟦ C ⟧ g ▢ m) (α C f (<–-wc ef) (<–-wc eg)) ∙
    ! (α C g f (⟦ C ⟧ <–-wc ef ▢ <–-wc eg))  

Type-wc : (i : ULevel) → WildCat {lsucc i} {i}
ob (Type-wc i) = Type i
hom (Type-wc i) A B = A → B
id₁ (Type-wc i) = idf
_▢_ (Type-wc i) g f = g ∘ f
ρ (Type-wc i) = λ _ → idp
lamb (Type-wc i) = λ _ → idp
α (Type-wc i) = λ _ _ _ → idp
