{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.wild-cats.WildCat
open import lib.wild-cats.WildFunctor

module lib.wild-cats.WildNatTr where

module _ {ℓv ℓe : ULevel} {ℓ₁ ℓ₂} {D : WildCat {ℓv} {ℓe}} {C : WildCat {ℓ₁} {ℓ₂}} where

  record Nat-trans (F₁ F₂ : Functor-wc D C) : Type (lmax (lmax ℓv ℓe) (lmax ℓ₁ ℓ₂)) where
    constructor nattrans
    field
      comp : (x : ob D) → hom C (obj F₁ x) (obj F₂ x)
      sq : {x y : ob D} (f : hom D x y) → ⟦ C ⟧ arr F₂ f ▢ comp x == ⟦ C ⟧ comp y ▢ arr F₁ f  
  open Nat-trans

  infixr 70 _Nat-trans-∘_
  _Nat-trans-∘_ : {F₁ F₂ F₃ : Functor-wc D C} → Nat-trans F₂ F₃ → Nat-trans F₁ F₂ → Nat-trans F₁ F₃
  comp (_Nat-trans-∘_ τ₂ τ₁) x = ⟦ C ⟧ comp τ₂ x ▢ comp τ₁ x
  sq (_Nat-trans-∘_ {F₁} {F₂} {F₃} τ₂ τ₁) {x} {y} f = 
    ⟦ C ⟧ arr F₃ f ▢ ⟦ C ⟧ comp τ₂ x ▢ comp τ₁ x
      =⟨ ! (α C (arr F₃ f) (comp τ₂ x) (comp τ₁ x)) ⟩
    ⟦ C ⟧ (⟦ C ⟧ arr F₃ f ▢  comp τ₂ x) ▢ comp τ₁ x
      =⟨ ap (λ m → ⟦ C ⟧ m ▢ comp τ₁ x) (sq τ₂ f) ⟩
    ⟦ C ⟧ (⟦ C ⟧ comp τ₂ y ▢ arr F₂ f) ▢ comp τ₁ x
      =⟨ α C (comp τ₂ y) (arr F₂ f) (comp τ₁ x) ⟩
    ⟦ C ⟧ comp τ₂ y ▢ ⟦ C ⟧ arr F₂ f ▢ comp τ₁ x
      =⟨ ap (λ m → ⟦ C ⟧ comp τ₂ y ▢ m) (sq τ₁ f) ⟩
    ⟦ C ⟧ comp τ₂ y ▢ ⟦ C ⟧ comp τ₁ y ▢ arr F₁ f
      =⟨ ! (α C (comp τ₂ y) (comp τ₁ y) (arr F₁ f)) ⟩
    ⟦ C ⟧ (⟦ C ⟧ comp τ₂ y ▢ comp τ₁ y) ▢ arr F₁ f =∎

  Nat-iso : Functor-wc D C → Functor-wc D C → Type (lmax (lmax (lmax ℓv ℓe) ℓ₁) ℓ₂)
  Nat-iso F₁ F₂ = Σ (Nat-trans F₁ F₂) (λ τ → (x : ob D) → equiv-wc C (comp τ x))

  Nat-iso-rev : {F₁ F₂ : Functor-wc D C} → Nat-iso F₁ F₂ → Nat-iso F₂ F₁
  comp (fst (Nat-iso-rev (_ , iso))) x = <–-wc C (iso x)
  sq (fst (Nat-iso-rev {F₁} {F₂} (τ , iso))) {x} {y} f = 
    ⟦ C ⟧ arr F₁ f ▢ <–-wc C (iso x)
      =⟨ ap (λ m → ⟦ C ⟧ m ▢ <–-wc C (iso x)) (lamb C (arr F₁ f)) ⟩
    ⟦ C ⟧ (⟦ C ⟧ id₁ C (obj F₁ y) ▢ arr F₁ f) ▢ <–-wc C (iso x)
      =⟨ ap (λ m → ⟦ C ⟧ (⟦ C ⟧ m ▢ arr F₁ f) ▢ <–-wc C (iso x)) (<–-wc-linv C (iso y)) ⟩
    ⟦ C ⟧ (⟦ C ⟧ (⟦ C ⟧ <–-wc C (iso y) ▢ comp τ y) ▢ arr F₁ f) ▢ <–-wc C (iso x)
      =⟨ ap (λ m → ⟦ C ⟧ m ▢ <–-wc C (iso x)) (α C (<–-wc C (iso y)) (comp τ y) (arr F₁ f)) ⟩
    ⟦ C ⟧ (⟦ C ⟧ <–-wc C (iso y) ▢ ⟦ C ⟧ comp τ y ▢ arr F₁ f) ▢ <–-wc C (iso x)
      =⟨ ap (λ m → ⟦ C ⟧ (⟦ C ⟧ <–-wc C (iso y) ▢ m) ▢ <–-wc C (iso x)) (! (sq τ f)) ⟩
    ⟦ C ⟧ (⟦ C ⟧ <–-wc C (iso y) ▢ (⟦ C ⟧ arr F₂ f ▢ comp τ x)) ▢ <–-wc C (iso x)
      =⟨ α C (<–-wc C (iso y)) (⟦ C ⟧ arr F₂ f ▢ comp τ x) (<–-wc C (iso x)) ⟩
    ⟦ C ⟧ <–-wc C (iso y) ▢ (⟦ C ⟧ (⟦ C ⟧ arr F₂ f ▢ comp τ x) ▢ <–-wc C (iso x))
      =⟨ ap (λ m → ⟦ C ⟧ <–-wc C (iso y) ▢ m) (α C (arr F₂ f) (comp τ x) (<–-wc C (iso x))) ⟩
    ⟦ C ⟧ <–-wc C (iso y) ▢ ⟦ C ⟧ arr F₂ f ▢ ⟦ C ⟧ comp τ x ▢ <–-wc C (iso x)
      =⟨ ap (λ m → ⟦ C ⟧ <–-wc C (iso y) ▢ ⟦ C ⟧ arr F₂ f ▢ m) (! (<–-wc-rinv C (iso x))) ⟩
    ⟦ C ⟧ <–-wc C (iso y) ▢ ⟦ C ⟧ arr F₂ f ▢ id₁ C (obj F₂ x)
      =⟨ ap (λ m → ⟦ C ⟧ <–-wc C (iso y) ▢ m) (! (ρ C (arr F₂ f))) ⟩
    ⟦ C ⟧ <–-wc C (iso y) ▢ arr F₂ f =∎
  snd (Nat-iso-rev (_ , iso)) x = equiv-wc-rev C (iso x)

open Nat-trans

module _ {ℓv ℓe : ULevel} {ℓc₁ ℓc₂ ℓd₁ ℓd₂} {I : WildCat {ℓv} {ℓe}} {C : WildCat {ℓc₁} {ℓc₂}} {D : WildCat {ℓd₁} {ℓd₂}}
  {F₁ F₂ : Functor-wc I C} where

  nat-trans-whisk-r : (τ : Nat-trans F₁ F₂) (G : Functor-wc C D) → Nat-trans (G ∘WC F₁) (G ∘WC F₂)
  comp (nat-trans-whisk-r τ G) x = arr G (comp τ x)
  sq (nat-trans-whisk-r τ G) {x} {y} f = 
    ⟦ D ⟧ arr G (arr F₂ f) ▢ arr G (comp τ x)
      =⟨ ! (comp G (comp τ x) (arr F₂ f)) ⟩
    arr G (⟦ C ⟧ arr F₂ f ▢ comp τ x)
      =⟨ ap (arr G) (sq τ f) ⟩
    arr G (⟦ C ⟧ comp τ y ▢ arr F₁ f)
      =⟨ comp G (arr F₁ f) (comp τ y) ⟩
    ⟦ D ⟧ arr G (comp τ y) ▢ arr G (arr F₁ f) =∎

  nat-trans-whisk-l : (τ : Nat-trans F₁ F₂) (G : Functor-wc D I) → Nat-trans (F₁ ∘WC G) (F₂ ∘WC G)
  comp (nat-trans-whisk-l τ G) x = comp τ (obj G x)
  sq (nat-trans-whisk-l τ G) {x} {y} f = sq τ (arr G f)
  
  nat-iso-whisk-r : (τ : Nat-iso F₁ F₂) (G : Functor-wc C D) → Nat-iso (G ∘WC F₁) (G ∘WC F₂)
  fst (nat-iso-whisk-r τ G) = nat-trans-whisk-r (fst τ) G
  snd (nat-iso-whisk-r τ G) x = F-equiv-wc G (snd τ x)

  nat-iso-whisk-l : (τ : Nat-iso F₁ F₂) (G : Functor-wc D I) → Nat-iso (F₁ ∘WC G) (F₂ ∘WC G)
  fst (nat-iso-whisk-l τ G) = nat-trans-whisk-l (fst τ) G
  snd (nat-iso-whisk-l τ G) x = snd τ (obj G x)

module _ {ℓc₁ ℓc₂ ℓd₁ ℓd₂ : ULevel} (C : WildCat {ℓc₁} {ℓc₂}) (D : WildCat {ℓd₁} {ℓd₂}) where

  record Equiv-wc : Type (lmax (lmax ℓc₁ ℓc₂) (lmax ℓd₁ ℓd₂)) where
    field
      ftor₁ : Functor-wc C D
      ftor₂ : Functor-wc D C
      iso₁ : Nat-iso (ftor₁ ∘WC ftor₂) (idfWC D)
      iso₂ : Nat-iso (idfWC C) (ftor₂ ∘WC ftor₁)
  open Equiv-wc

  record AdjEquiv-wc : Type (lmax (lmax ℓc₁ ℓc₂) (lmax ℓd₁ ℓd₂)) where
    field
      𝔼 : Equiv-wc
      zig-zag : (x : ob C) →
        ⟦ D ⟧ comp (fst (iso₁ 𝔼)) (obj (ftor₁ 𝔼) x) ▢ arr (ftor₁ 𝔼) (comp (fst (iso₂ 𝔼)) x) == id₁ D (obj (ftor₁ 𝔼) x)

module _ {ℓc₁ ℓc₂ ℓd₁ ℓd₂ : ULevel} {C : WildCat {ℓc₁} {ℓc₂}} {D : WildCat {ℓd₁} {ℓd₂}} where

  open Equiv-wc
  open AdjEquiv-wc

  Equiv-wc-promote : Equiv-wc C D → AdjEquiv-wc C D
  ftor₁ (𝔼 (Equiv-wc-promote e)) = ftor₁ e
  ftor₂ (𝔼 (Equiv-wc-promote e)) = ftor₂ e
  comp (fst (iso₁ (𝔼 (Equiv-wc-promote e)))) x =
    ⟦ D ⟧ comp (fst (iso₁ e)) x ▢
    ⟦ D ⟧ <–-wc D (F-equiv-wc (ftor₁ e) (snd (iso₂ e) (obj (ftor₂ e) x))) ▢
    <–-wc D (snd (iso₁ e) (obj (ftor₁ e) (obj (ftor₂ e) x)))
  sq (fst (iso₁ (𝔼 (Equiv-wc-promote e)))) {x} {y} f = 
    ⟦ D ⟧ f ▢
    ⟦ D ⟧ comp (fst (iso₁ e)) x ▢
    ⟦ D ⟧ <–-wc D (F-equiv-wc (ftor₁ e) (snd (iso₂ e) (obj (ftor₂ e) x))) ▢
    <–-wc D (snd (iso₁ e) (obj (ftor₁ e) (obj (ftor₂ e) x)))
      =⟨ ! (α D f (comp (fst (iso₁ e)) x)
           (⟦ D ⟧ <–-wc D (F-equiv-wc (ftor₁ e) (snd (iso₂ e) (obj (ftor₂ e) x))) ▢
           <–-wc D (snd (iso₁ e) (obj (ftor₁ e) (obj (ftor₂ e) x))))) ⟩
    ⟦ D ⟧ (⟦ D ⟧ f ▢ comp (fst (iso₁ e)) x) ▢
    (⟦ D ⟧ <–-wc D (F-equiv-wc (ftor₁ e) (snd (iso₂ e) (obj (ftor₂ e) x))) ▢
    <–-wc D (snd (iso₁ e) (obj (ftor₁ e) (obj (ftor₂ e) x))))
      =⟨ ap (λ m →
           ⟦ D ⟧ m ▢
             ⟦ D ⟧ <–-wc D (F-equiv-wc (ftor₁ e) (snd (iso₂ e) (obj (ftor₂ e) x))) ▢
             <–-wc D (snd (iso₁ e) (obj (ftor₁ e) (obj (ftor₂ e) x))))
          (sq (fst (iso₁ e)) f) ⟩
    ⟦ D ⟧ (⟦ D ⟧ comp (fst (iso₁ e)) y ▢ arr (ftor₁ e) (arr (ftor₂ e) f)) ▢
    ⟦ D ⟧ <–-wc D (F-equiv-wc (ftor₁ e) (snd (iso₂ e) (obj (ftor₂ e) x))) ▢
    <–-wc D (snd (iso₁ e) (obj (ftor₁ e) (obj (ftor₂ e) x)))
      =⟨ α D (comp (fst (iso₁ e)) y) (arr (ftor₁ e) (arr (ftor₂ e) f))
           (⟦ D ⟧ <–-wc D (F-equiv-wc (ftor₁ e) (snd (iso₂ e) (obj (ftor₂ e) x))) ▢
           <–-wc D (snd (iso₁ e) (obj (ftor₁ e) (obj (ftor₂ e) x)))) ⟩
    ⟦ D ⟧ comp (fst (iso₁ e)) y ▢
    ⟦ D ⟧ arr (ftor₁ e) (arr (ftor₂ e) f) ▢
    ⟦ D ⟧ <–-wc D (F-equiv-wc (ftor₁ e) (snd (iso₂ e) (obj (ftor₂ e) x))) ▢
    <–-wc D (snd (iso₁ e) (obj (ftor₁ e) (obj (ftor₂ e) x)))
      =⟨ ap (λ m → ⟦ D ⟧ comp (fst (iso₁ e)) y ▢ m)
           (! (α D
                (arr (ftor₁ e) (arr (ftor₂ e) f))
                (<–-wc D (F-equiv-wc (ftor₁ e) (snd (iso₂ e) (obj (ftor₂ e) x))))
                (<–-wc D (snd (iso₁ e) (obj (ftor₁ e) (obj (ftor₂ e) x)))))) ⟩
    ⟦ D ⟧ comp (fst (iso₁ e)) y ▢
    ⟦ D ⟧ (⟦ D ⟧ arr (ftor₁ e) (arr (ftor₂ e) f) ▢
    <–-wc D (F-equiv-wc (ftor₁ e) (snd (iso₂ e) (obj (ftor₂ e) x)))) ▢
    <–-wc D (snd (iso₁ e) (obj (ftor₁ e) (obj (ftor₂ e) x)))
      =⟨ ap (λ m → ⟦ D ⟧ comp (fst (iso₁ e)) y ▢ ⟦ D ⟧ m ▢ <–-wc D (snd (iso₁ e) (obj (ftor₁ e) (obj (ftor₂ e) x)))) (
           sq (fst (Nat-iso-rev (nat-iso-whisk-r (nat-iso-whisk-l (iso₂ e) (ftor₂ e)) (ftor₁ e)))) f) ⟩
    ⟦ D ⟧ comp (fst (iso₁ e)) y ▢
    ⟦ D ⟧ (⟦ D ⟧ <–-wc D (F-equiv-wc (ftor₁ e) (snd (iso₂ e) (obj (ftor₂ e) y))) ▢
      (arr (ftor₁ e) ∘ (arr (ftor₂ e) ∘ arr (ftor₁ e)) ∘ arr (ftor₂ e)) f) ▢
    <–-wc D (snd (iso₁ e) (obj (ftor₁ e) (obj (ftor₂ e) x)))
      =⟨ ap (λ m → ⟦ D ⟧ comp (fst (iso₁ e)) y ▢ m)
           (α D
             (<–-wc D (F-equiv-wc (ftor₁ e) (snd (iso₂ e) (obj (ftor₂ e) y))))
             ((arr (ftor₁ e) ∘ (arr (ftor₂ e) ∘ arr (ftor₁ e)) ∘ arr (ftor₂ e)) f)
             (<–-wc D (snd (iso₁ e) (obj (ftor₁ e) (obj (ftor₂ e) x))))) ⟩
    ⟦ D ⟧ comp (fst (iso₁ e)) y ▢
    ⟦ D ⟧ <–-wc D (F-equiv-wc (ftor₁ e) (snd (iso₂ e) (obj (ftor₂ e) y))) ▢
    ⟦ D ⟧ (arr (ftor₁ e) ∘ (arr (ftor₂ e) ∘ arr (ftor₁ e)) ∘ arr (ftor₂ e)) f ▢
    <–-wc D (snd (iso₁ e) (obj (ftor₁ e) (obj (ftor₂ e) x)))
      =⟨ ap (λ m → ⟦ D ⟧ comp (fst (iso₁ e)) y ▢ ⟦ D ⟧ <–-wc D (F-equiv-wc (ftor₁ e) (snd (iso₂ e) (obj (ftor₂ e) y))) ▢ m)
           (sq (fst (Nat-iso-rev (nat-iso-whisk-l (iso₁ e) (ftor₁ e ∘WC ftor₂ e)))) f) ⟩
    ⟦ D ⟧ comp (fst (iso₁ e)) y ▢
    ⟦ D ⟧ <–-wc D (F-equiv-wc (ftor₁ e) (snd (iso₂ e) (obj (ftor₂ e) y))) ▢
    ⟦ D ⟧ <–-wc D (snd (iso₁ e) ((obj (ftor₁ e) ∘ obj (ftor₂ e)) y)) ▢
    arr (ftor₁ e) (arr (ftor₂ e) f)
      =⟨ ap (λ m → ⟦ D ⟧ comp (fst (iso₁ e)) y ▢ m) (!
           (α D
             (<–-wc D (F-equiv-wc (ftor₁ e) (snd (iso₂ e) (obj (ftor₂ e) y))))
             (<–-wc D (snd (iso₁ e) ((obj (ftor₁ e) ∘ obj (ftor₂ e)) y)))
             (arr (ftor₁ e) (arr (ftor₂ e) f)))) ⟩
    ⟦ D ⟧ comp (fst (iso₁ e)) y ▢
    ⟦ D ⟧ (⟦ D ⟧ <–-wc D (F-equiv-wc (ftor₁ e) (snd (iso₂ e) (obj (ftor₂ e) y))) ▢
      <–-wc D (snd (iso₁ e) ((obj (ftor₁ e) ∘ obj (ftor₂ e)) y))) ▢
    arr (ftor₁ e) (arr (ftor₂ e) f)
      =⟨ ! (α D
             (comp (fst (iso₁ e)) y)
             (⟦ D ⟧ <–-wc D (F-equiv-wc (ftor₁ e) (snd (iso₂ e) (obj (ftor₂ e) y))) ▢
               <–-wc D (snd (iso₁ e) ((obj (ftor₁ e) ∘ obj (ftor₂ e)) y)))
             (arr (ftor₁ e) (arr (ftor₂ e) f))) ⟩
    ⟦ D ⟧ (⟦ D ⟧ comp (fst (iso₁ e)) y ▢
      (⟦ D ⟧ <–-wc D (F-equiv-wc (ftor₁ e) (snd (iso₂ e) (obj (ftor₂ e) y))) ▢
        <–-wc D (snd (iso₁ e) (obj (ftor₁ e) (obj (ftor₂ e) y))))) ▢
    arr (ftor₁ e) (arr (ftor₂ e) f) =∎
  snd (iso₁ (𝔼 (Equiv-wc-promote e))) x = equiv-wc-∘ D (snd (iso₁ e) x)
    (equiv-wc-∘ D (equiv-wc-rev D (F-equiv-wc (ftor₁ e) (snd (iso₂ e) (obj (ftor₂ e) x))))
      (equiv-wc-rev D (snd (iso₁ e) (obj (ftor₁ e) (obj (ftor₂ e) x)))))
  iso₂ (𝔼 (Equiv-wc-promote e)) = iso₂ e
  zig-zag (Equiv-wc-promote e) x = {!!}
