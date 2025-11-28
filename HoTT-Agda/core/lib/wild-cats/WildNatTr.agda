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
      =⟨ α C (arr F₃ f) (comp τ₂ x) (comp τ₁ x) ⟩
    ⟦ C ⟧ (⟦ C ⟧ arr F₃ f ▢ comp τ₂ x) ▢ comp τ₁ x
      =⟨ ap (λ m → ⟦ C ⟧ m ▢ comp τ₁ x) (sq τ₂ f) ⟩
    ⟦ C ⟧ (⟦ C ⟧ comp τ₂ y ▢ arr F₂ f) ▢ comp τ₁ x
      =⟨ ! (α C (comp τ₂ y) (arr F₂ f) (comp τ₁ x)) ⟩
    ⟦ C ⟧ comp τ₂ y ▢ ⟦ C ⟧ arr F₂ f ▢ comp τ₁ x
      =⟨ ap (λ m → ⟦ C ⟧ comp τ₂ y ▢ m) (sq τ₁ f) ⟩
    ⟦ C ⟧ comp τ₂ y ▢ ⟦ C ⟧ comp τ₁ y ▢ arr F₁ f
      =⟨ α C (comp τ₂ y) (comp τ₁ y) (arr F₁ f) ⟩
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
      =⟨ ! (ap (λ m → ⟦ C ⟧ m ▢ <–-wc C (iso x)) (α C (<–-wc C (iso y)) (comp τ y) (arr F₁ f))) ⟩
    ⟦ C ⟧ (⟦ C ⟧ <–-wc C (iso y) ▢ ⟦ C ⟧ comp τ y ▢ arr F₁ f) ▢ <–-wc C (iso x)
      =⟨ ap (λ m → ⟦ C ⟧ (⟦ C ⟧ <–-wc C (iso y) ▢ m) ▢ <–-wc C (iso x)) (! (sq τ f)) ⟩
    ⟦ C ⟧ (⟦ C ⟧ <–-wc C (iso y) ▢ (⟦ C ⟧ arr F₂ f ▢ comp τ x)) ▢ <–-wc C (iso x)
      =⟨ ! (α C (<–-wc C (iso y)) (⟦ C ⟧ arr F₂ f ▢ comp τ x) (<–-wc C (iso x))) ⟩
    ⟦ C ⟧ <–-wc C (iso y) ▢ (⟦ C ⟧ (⟦ C ⟧ arr F₂ f ▢ comp τ x) ▢ <–-wc C (iso x))
      =⟨ ! (ap (λ m → ⟦ C ⟧ <–-wc C (iso y) ▢ m) (α C (arr F₂ f) (comp τ x) (<–-wc C (iso x)))) ⟩
    ⟦ C ⟧ <–-wc C (iso y) ▢ ⟦ C ⟧ arr F₂ f ▢ ⟦ C ⟧ comp τ x ▢ <–-wc C (iso x)
      =⟨ ap (λ m → ⟦ C ⟧ <–-wc C (iso y) ▢ ⟦ C ⟧ arr F₂ f ▢ m) (! (<–-wc-rinv C (iso x))) ⟩
    ⟦ C ⟧ <–-wc C (iso y) ▢ ⟦ C ⟧ arr F₂ f ▢ id₁ C (obj F₂ x)
      =⟨ ap (λ m → ⟦ C ⟧ <–-wc C (iso y) ▢ m) (! (ρ C (arr F₂ f))) ⟩
    ⟦ C ⟧ <–-wc C (iso y) ▢ arr F₂ f =∎
  snd (Nat-iso-rev (_ , iso)) x = equiv-wc-rev C (iso x)

open Nat-trans

module _ {ℓv ℓe : ULevel} {ℓc₁ ℓc₂ ℓd₁ ℓd₂} {I : WildCat {ℓv} {ℓe}} {C : WildCat {ℓc₁} {ℓc₂}} {D : WildCat {ℓd₁} {ℓd₂}}
  {F₁ F₂ : Functor-wc I C} where

  nat-trans-whisk-l : (τ : Nat-trans F₁ F₂) (G : Functor-wc C D) → Nat-trans (G ∘WC F₁) (G ∘WC F₂)
  comp (nat-trans-whisk-l τ G) x = arr G (comp τ x)
  sq (nat-trans-whisk-l τ G) {x} {y} f = 
    ⟦ D ⟧ arr G (arr F₂ f) ▢ arr G (comp τ x)
      =⟨ ! (comp G (comp τ x) (arr F₂ f)) ⟩
    arr G (⟦ C ⟧ arr F₂ f ▢ comp τ x)
      =⟨ ap (arr G) (sq τ f) ⟩
    arr G (⟦ C ⟧ comp τ y ▢ arr F₁ f)
      =⟨ comp G (arr F₁ f) (comp τ y) ⟩
    ⟦ D ⟧ arr G (comp τ y) ▢ arr G (arr F₁ f) =∎

  nat-trans-whisk-r : (τ : Nat-trans F₁ F₂) (G : Functor-wc D I) → Nat-trans (F₁ ∘WC G) (F₂ ∘WC G)
  comp (nat-trans-whisk-r τ G) x = comp τ (obj G x)
  sq (nat-trans-whisk-r τ G) f = sq τ (arr G f)
  
  nat-iso-whisk-l : (τ : Nat-iso F₁ F₂) (G : Functor-wc C D) → Nat-iso (G ∘WC F₁) (G ∘WC F₂)
  fst (nat-iso-whisk-l τ G) = nat-trans-whisk-l (fst τ) G
  snd (nat-iso-whisk-l τ G) x = F-equiv-wc G (snd τ x)

  nat-iso-whisk-r : (τ : Nat-iso F₁ F₂) (G : Functor-wc D I) → Nat-iso (F₁ ∘WC G) (F₂ ∘WC G)
  fst (nat-iso-whisk-r τ G) = nat-trans-whisk-r (fst τ) G
  snd (nat-iso-whisk-r τ G) x = snd τ (obj G x)

module _ {ℓc₁ ℓc₂ ℓd₁ ℓd₂ : ULevel} (C : WildCat {ℓc₁} {ℓc₂}) (D : WildCat {ℓd₁} {ℓd₂}) where

  -- equivalence between wild categories
  record Equiv-wc : Type (lmax (lmax ℓc₁ ℓc₂) (lmax ℓd₁ ℓd₂)) where
    constructor EquivWC
    field
      ftor₁ : Functor-wc C D
      ftor₂ : Functor-wc D C
      iso₁ : Nat-iso (ftor₁ ∘WC ftor₂) (idfWC D)
      iso₂ : Nat-iso (idfWC C) (ftor₂ ∘WC ftor₁)
      
    iso₁-coher : (x : ob D) → arr ftor₁ (arr ftor₂ (comp (fst iso₁) x)) == comp (fst iso₁) (obj ftor₁ (obj ftor₂ x))
    iso₁-coher x =
      arr ftor₁ (arr ftor₂ (comp (fst iso₁) x))
        =⟨ lamb D (arr ftor₁ (arr ftor₂ (comp (fst iso₁) x))) ⟩
      ⟦ D ⟧ id₁ D (obj ftor₁ (obj ftor₂ x)) ▢ arr ftor₁ (arr ftor₂ (comp (fst iso₁) x))
        =⟨ ap (λ m → ⟦ D ⟧ m ▢ arr ftor₁ (arr ftor₂ (comp (fst iso₁) x))) (<–-wc-linv D (snd iso₁ x)) ⟩
      ⟦ D ⟧ ⟦ D ⟧ <–-wc D (snd iso₁ x) ▢ comp (fst iso₁) x ▢ arr ftor₁ (arr ftor₂ (comp (fst iso₁) x))
        =⟨ ! (α D (<–-wc D (snd iso₁ x)) (comp (fst iso₁) x) (arr ftor₁ (arr ftor₂ (comp (fst iso₁) x)))) ⟩
      ⟦ D ⟧ <–-wc D (snd iso₁ x) ▢ ⟦ D ⟧ comp (fst iso₁) x ▢ arr ftor₁ (arr ftor₂ (comp (fst iso₁) x))
        =⟨ ap (λ m → ⟦ D ⟧ <–-wc D ((snd iso₁) x) ▢ m) (! (sq (fst iso₁) (comp (fst iso₁) x))) ⟩
      ⟦ D ⟧ <–-wc D (snd iso₁ x) ▢ ⟦ D ⟧ comp (fst iso₁) x ▢ comp (fst iso₁) (obj ftor₁ (obj ftor₂ x))
        =⟨ α D (fst (snd iso₁ x)) (comp (fst iso₁) x) (comp (fst iso₁) (obj ftor₁ (obj ftor₂ x))) ⟩
      ⟦ D ⟧ ⟦ D ⟧ <–-wc D (snd iso₁ x) ▢ comp (fst iso₁) x ▢ comp (fst iso₁) (obj ftor₁ (obj ftor₂ x))
        =⟨ ap (λ m → ⟦ D ⟧ m ▢ comp (fst iso₁) (obj ftor₁ (obj ftor₂ x))) (! (<–-wc-linv D (snd iso₁ x))) ⟩
      ⟦ D ⟧ id₁ D (obj ftor₁ (obj ftor₂ x)) ▢ comp (fst iso₁) (obj ftor₁ (obj ftor₂ x))
        =⟨ ! (lamb D (comp (fst iso₁) (obj ftor₁ (obj ftor₂ x)))) ⟩
      comp (fst iso₁) (obj ftor₁ (obj ftor₂ x)) =∎
      
    iso₂-coher : (x : ob C) → arr ftor₂ (arr ftor₁ (comp (fst iso₂) x)) == comp (fst iso₂) (obj ftor₂ (obj ftor₁ x))
    iso₂-coher x = 
      arr ftor₂ (arr ftor₁ (comp (fst iso₂) x))
        =⟨ ρ C (arr ftor₂ (arr ftor₁ (comp (fst iso₂) x))) ⟩
      ⟦ C ⟧ arr ftor₂ (arr ftor₁ (comp (fst iso₂) x)) ▢ id₁ C (obj ftor₂ (obj ftor₁ x))
        =⟨ ap (λ m → ⟦ C ⟧ arr ftor₂ (arr ftor₁ (comp (fst iso₂) x)) ▢ m) (<–-wc-rinv C (snd iso₂ x)) ⟩
      ⟦ C ⟧ arr ftor₂ (arr ftor₁ (comp (fst iso₂) x)) ▢ ⟦ C ⟧ comp (fst iso₂) x ▢ <–-wc C ((snd iso₂) x)
        =⟨ α C (arr ftor₂ (arr ftor₁ (comp (fst iso₂) x))) (comp (fst iso₂) x) (<–-wc C ((snd iso₂) x)) ⟩
      ⟦ C ⟧ ⟦ C ⟧ arr ftor₂ (arr ftor₁ (comp (fst iso₂) x)) ▢ comp (fst iso₂) x ▢ <–-wc C ((snd iso₂) x)
        =⟨ ap (λ m → ⟦ C ⟧ m ▢ <–-wc C ((snd iso₂) x)) (sq (fst iso₂) (comp (fst iso₂) x)) ⟩
      ⟦ C ⟧ ⟦ C ⟧ comp (fst iso₂) (obj ftor₂ (obj ftor₁ x)) ▢ comp (fst iso₂) x ▢ <–-wc C (snd iso₂ x)
        =⟨ ! (α C (comp (fst iso₂) (obj ftor₂ (obj ftor₁ x))) (comp (fst iso₂) x) (<–-wc C (snd iso₂ x))) ⟩
      ⟦ C ⟧ comp (fst iso₂) (obj ftor₂ (obj ftor₁ x)) ▢ ⟦ C ⟧ comp (fst iso₂) x ▢ <–-wc C (snd iso₂ x)
        =⟨ ap (λ m → ⟦ C ⟧ comp (fst iso₂) (obj ftor₂ (obj ftor₁ x)) ▢ m) (! (<–-wc-rinv C (snd iso₂ x))) ⟩
      ⟦ C ⟧ comp (fst iso₂) (obj ftor₂ (obj ftor₁ x)) ▢ id₁ C (obj ftor₂ (obj ftor₁ x))
        =⟨ ! (ρ C (comp (fst iso₂) (obj ftor₂ (obj ftor₁ x)))) ⟩
      comp (fst iso₂) (obj ftor₂ (obj ftor₁ x)) =∎
      
    iso₁-coher-inv : (x : ob D) →
      <–-wc D (F-equiv-wc (ftor₁ ∘WC ftor₂) (snd iso₁ x)) == <–-wc D (snd iso₁ (obj ftor₁ (obj ftor₂ x)))
    iso₁-coher-inv x = ap-<–-wc D (iso₁-coher x) (F-equiv-wc (ftor₁ ∘WC ftor₂) (snd iso₁ x)) (snd iso₁ (obj ftor₁ (obj ftor₂ x)))
    
    iso₂-coher-inv : (x : ob C) →
      <–-wc C (F-equiv-wc (ftor₂ ∘WC ftor₁) (snd iso₂ x)) == <–-wc C (snd iso₂ (obj ftor₂ (obj ftor₁ x)))
    iso₂-coher-inv x = ap-<–-wc C (iso₂-coher x) (F-equiv-wc (ftor₂ ∘WC ftor₁) (snd iso₂ x)) (snd iso₂ (obj ftor₂ (obj ftor₁ x)))
    
    sq-inv₁ : ∀ {x} {y} (f : hom D x y) → ⟦ D ⟧ arr ftor₁ (arr ftor₂ f) ▢ <–-wc D (snd iso₁ x) == ⟦ D ⟧ <–-wc D (snd iso₁ y) ▢ f
    sq-inv₁ {x} {y} f = 
      ⟦ D ⟧ arr ftor₁ (arr ftor₂ f) ▢ <–-wc D (snd iso₁ x)
        =⟨ lamb D (⟦ D ⟧ arr ftor₁ (arr ftor₂ f) ▢ fst (snd iso₁ x)) ⟩
      ⟦ D ⟧ id₁ D (obj ftor₁ (obj ftor₂ y)) ▢ ⟦ D ⟧ arr ftor₁ (arr ftor₂ f) ▢ <–-wc D (snd iso₁ x)
        =⟨ ap (λ m → ⟦ D ⟧ m ▢ ⟦ D ⟧ arr ftor₁ (arr ftor₂ f) ▢ <–-wc D (snd iso₁ x)) (<–-wc-linv D (snd iso₁ y)) ⟩
      ⟦ D ⟧ ⟦ D ⟧ <–-wc D (snd iso₁ y) ▢ comp (fst iso₁) y ▢ ⟦ D ⟧ arr ftor₁ (arr ftor₂ f) ▢ <–-wc D (snd iso₁ x)
        =⟨ ! (α D (<–-wc D (snd iso₁ y)) (comp (fst iso₁) y) (⟦ D ⟧ arr ftor₁ (arr ftor₂ f) ▢ <–-wc D (snd iso₁ x))) ⟩
      ⟦ D ⟧ <–-wc D (snd iso₁ y) ▢ ⟦ D ⟧ comp (fst iso₁) y ▢ ⟦ D ⟧ arr ftor₁ (arr ftor₂ f) ▢ <–-wc D (snd iso₁ x)
        =⟨ ap (λ m → ⟦ D ⟧ <–-wc D (snd iso₁ y) ▢ m) (α D (comp (fst iso₁) y) (arr ftor₁ (arr ftor₂ f)) (<–-wc D (snd iso₁ x))) ⟩
      ⟦ D ⟧ <–-wc D (snd iso₁ y) ▢ ⟦ D ⟧ ⟦ D ⟧ comp (fst iso₁) y ▢ arr ftor₁ (arr ftor₂ f) ▢ <–-wc D (snd iso₁ x)
        =⟨ ap (λ m → ⟦ D ⟧ <–-wc D (snd iso₁ y) ▢ ⟦ D ⟧ m ▢ <–-wc D (snd iso₁ x)) (! (sq (fst iso₁) f)) ⟩
      ⟦ D ⟧ <–-wc D (snd iso₁ y) ▢ ⟦ D ⟧ ⟦ D ⟧ f ▢ comp (fst iso₁) x ▢ <–-wc D (snd iso₁ x)
        =⟨ ! (ap (λ m → ⟦ D ⟧ <–-wc D (snd iso₁ y) ▢ m) (α D f (comp (fst iso₁) x) (<–-wc D (snd iso₁ x)))) ⟩
      ⟦ D ⟧ <–-wc D (snd iso₁ y) ▢ ⟦ D ⟧ f ▢ ⟦ D ⟧ comp (fst iso₁) x ▢ <–-wc D (snd iso₁ x)
        =⟨ ap (λ m → ⟦ D ⟧ <–-wc D (snd iso₁ y) ▢ ⟦ D ⟧ f ▢ m) (! (<–-wc-rinv D (snd iso₁ x))) ⟩
      ⟦ D ⟧ <–-wc D (snd iso₁ y) ▢ ⟦ D ⟧ f ▢ id₁ D x
        =⟨ ap (λ m → ⟦ D ⟧ <–-wc D (snd iso₁ y) ▢ m) (! (ρ D f)) ⟩
      ⟦ D ⟧ <–-wc D (snd iso₁ y) ▢ f =∎
    
    sq-inv₂ : ∀ {x} {y} (f : hom C x y) → ⟦ C ⟧ f ▢ <–-wc C (snd iso₂ x) == ⟦ C ⟧ <–-wc C (snd iso₂ y) ▢ arr ftor₂ (arr ftor₁ f)
    sq-inv₂ {x} {y} f =
      ⟦ C ⟧ f ▢ <–-wc C (snd iso₂ x)
        =⟨ lamb C (⟦ C ⟧ f ▢ <–-wc C (snd iso₂ x)) ⟩
      ⟦ C ⟧ id₁ C y ▢ ⟦ C ⟧ f ▢ <–-wc C (snd iso₂ x)
        =⟨ ap (λ m → ⟦ C ⟧ m ▢ ⟦ C ⟧ f ▢ <–-wc C (snd iso₂ x)) (<–-wc-linv C (snd iso₂ y))  ⟩
      ⟦ C ⟧ ⟦ C ⟧ <–-wc C (snd iso₂ y) ▢ comp (fst iso₂) y ▢ ⟦ C ⟧ f ▢ <–-wc C (snd iso₂ x)
        =⟨ ! (α C (<–-wc C (snd iso₂ y)) (comp (fst iso₂) y) (⟦ C ⟧ f ▢ <–-wc C (snd iso₂ x))) ⟩
      ⟦ C ⟧ <–-wc C (snd iso₂ y) ▢  ⟦ C ⟧ comp (fst iso₂) y ▢ ⟦ C ⟧ f ▢ <–-wc C (snd iso₂ x)
        =⟨ ap (λ m → ⟦ C ⟧ <–-wc C (snd iso₂ y) ▢ m) (α C (comp (fst iso₂) y) f (<–-wc C (snd iso₂ x))) ⟩
      ⟦ C ⟧ <–-wc C (snd iso₂ y) ▢  ⟦ C ⟧ ⟦ C ⟧ comp (fst iso₂) y ▢ f ▢ <–-wc C (snd iso₂ x)
        =⟨ ap (λ m → ⟦ C ⟧ <–-wc C (snd iso₂ y) ▢  ⟦ C ⟧ m ▢ <–-wc C (snd iso₂ x)) (! (sq (fst iso₂) f)) ⟩
      ⟦ C ⟧ <–-wc C (snd iso₂ y) ▢  ⟦ C ⟧ ⟦ C ⟧ arr ftor₂ (arr ftor₁ f) ▢ comp (fst iso₂) x ▢ <–-wc C (snd iso₂ x)
        =⟨ ! (ap (λ m → ⟦ C ⟧ <–-wc C (snd iso₂ y) ▢ m) (α C (arr ftor₂ (arr ftor₁ f)) (comp (fst iso₂) x) (<–-wc C (snd iso₂ x)))) ⟩
      ⟦ C ⟧ <–-wc C (snd iso₂ y) ▢  ⟦ C ⟧ arr ftor₂ (arr ftor₁ f) ▢  ⟦ C ⟧ comp (fst iso₂) x ▢ <–-wc C (snd iso₂ x)
        =⟨ ap (λ m →  ⟦ C ⟧ <–-wc C (snd iso₂ y) ▢  ⟦ C ⟧ arr ftor₂ (arr ftor₁ f) ▢ m) (! (<–-wc-rinv C (snd iso₂ x))) ⟩
      ⟦ C ⟧ <–-wc C (snd iso₂ y) ▢  ⟦ C ⟧ arr ftor₂ (arr ftor₁ f) ▢  id₁ C (obj ftor₂ (obj ftor₁ x))
        =⟨ ap (λ m → ⟦ C ⟧ <–-wc C (snd iso₂ y) ▢ m) (! (ρ C (arr ftor₂ (arr ftor₁ f)))) ⟩
      ⟦ C ⟧ <–-wc C (snd iso₂ y) ▢ arr ftor₂ (arr ftor₁ f) =∎
      
  open Equiv-wc

  -- (component-wise) half-adjoint equivalence of wild cats
  record HAdjEquiv-wc : Type (lmax (lmax ℓc₁ ℓc₂) (lmax ℓd₁ ℓd₂)) where
    constructor AEquivWC
    field
      𝔼 : Equiv-wc
      zig-zag : (x : ob D) → ⟦ C ⟧ arr (ftor₂ 𝔼) (comp (fst (iso₁ 𝔼)) x) ▢ comp (fst (iso₂ 𝔼)) (obj (ftor₂ 𝔼) x) == id₁ C (obj (ftor₂ 𝔼) x)
 
    abstract
    
      zig-zag-rot : (x : ob D) → arr (ftor₂ 𝔼) (<–-wc D (snd (iso₁ 𝔼) x)) == comp (fst (iso₂ 𝔼)) (obj (ftor₂ 𝔼) x)
      zig-zag-rot x = 
        arr (ftor₂ 𝔼) (<–-wc D (snd (iso₁ 𝔼) x))
          =⟨ ρ C (arr (ftor₂ 𝔼) (<–-wc D (snd (iso₁ 𝔼) x))) ⟩
        ⟦ C ⟧ arr (ftor₂ 𝔼) (<–-wc D (snd (iso₁ 𝔼) x)) ▢ id₁ C (obj (ftor₂ 𝔼) x)
          =⟨ ! (ap (λ m → ⟦ C ⟧ arr (ftor₂ 𝔼) (<–-wc D (snd (iso₁ 𝔼) x)) ▢ m) (zig-zag x)) ⟩
        ⟦ C ⟧ arr (ftor₂ 𝔼) (<–-wc D (snd (iso₁ 𝔼) x)) ▢ ⟦ C ⟧ arr (ftor₂ 𝔼) (comp (fst (iso₁ 𝔼)) x) ▢ comp (fst (iso₂ 𝔼)) (obj (ftor₂ 𝔼) x)
          =⟨  α C (arr (ftor₂ 𝔼) (<–-wc D (snd (iso₁ 𝔼) x))) (arr (ftor₂ 𝔼) (comp (fst (iso₁ 𝔼)) x)) (comp (fst (iso₂ 𝔼)) (obj (ftor₂ 𝔼) x)) ⟩
        ⟦ C ⟧ ⟦ C ⟧ arr (ftor₂ 𝔼) (<–-wc D (snd (iso₁ 𝔼) x)) ▢ arr (ftor₂ 𝔼) (comp (fst (iso₁ 𝔼)) x) ▢ comp (fst (iso₂ 𝔼)) (obj (ftor₂ 𝔼) x)
          =⟨ ap (λ m → ⟦ C ⟧ m ▢  comp (fst (iso₂ 𝔼)) (obj (ftor₂ 𝔼) x)) (! (<–-wc-linv C (F-equiv-wc (ftor₂ 𝔼) (snd (iso₁ 𝔼) x)))) ⟩
        ⟦ C ⟧ id₁ C (obj (ftor₂ 𝔼) (obj (ftor₁ 𝔼) (obj (ftor₂ 𝔼) x))) ▢ comp (fst (iso₂ 𝔼)) (obj (ftor₂ 𝔼) x)
          =⟨ ! (lamb C (comp (fst (iso₂ 𝔼)) (obj (ftor₂ 𝔼) x))) ⟩
        comp (fst (iso₂ 𝔼)) (obj (ftor₂ 𝔼) x) =∎

      -- the other triangle equality is derivable:

      zig-zag-swap-aux : (x : ob C) →
        ⟦ D ⟧ arr (ftor₁ 𝔼) (arr (ftor₂ 𝔼) (arr (ftor₁ 𝔼) (comp (fst (iso₂ 𝔼)) x))) ▢ <–-wc D (snd (iso₁ 𝔼) (obj (ftor₁ 𝔼) x))
          ==
        ⟦ D ⟧ arr (ftor₁ 𝔼) (arr (ftor₂ 𝔼) (arr (ftor₁ 𝔼) (comp (fst (iso₂ 𝔼)) x))) ▢ arr (ftor₁ 𝔼) (comp (fst (iso₂ 𝔼)) x)
      zig-zag-swap-aux x = 
        ⟦ D ⟧ arr (ftor₁ 𝔼) (arr (ftor₂ 𝔼) (arr (ftor₁ 𝔼) (comp (fst (iso₂ 𝔼)) x))) ▢ <–-wc D (snd (iso₁ 𝔼) (obj (ftor₁ 𝔼) x))
          =⟨ sq-inv₁ 𝔼 (arr (ftor₁ 𝔼) (comp (fst (iso₂ 𝔼)) x)) ⟩
        ⟦ D ⟧ <–-wc D (snd (iso₁ 𝔼) (obj (ftor₁ 𝔼) (obj (ftor₂ 𝔼) (obj (ftor₁ 𝔼) x)))) ▢ arr (ftor₁ 𝔼) (comp (fst (iso₂ 𝔼)) x)
          =⟨ ap (λ m → ⟦ D ⟧ m ▢ arr (ftor₁ 𝔼) (comp (fst (iso₂ 𝔼)) x)) (! (iso₁-coher-inv 𝔼 (obj (ftor₁ 𝔼) x))) ⟩
        ⟦ D ⟧ <–-wc D (F-equiv-wc (ftor₁ 𝔼 ∘WC ftor₂ 𝔼) (snd (iso₁ 𝔼) (obj (ftor₁ 𝔼) x))) ▢ arr (ftor₁ 𝔼) (comp (fst (iso₂ 𝔼)) x)
          =⟨ ap (λ m → ⟦ D ⟧ m ▢ arr (ftor₁ 𝔼) (comp (fst (iso₂ 𝔼)) x)) (ap (arr (ftor₁ 𝔼)) (zig-zag-rot (obj (ftor₁ 𝔼) x))) ⟩
        ⟦ D ⟧ arr (ftor₁ 𝔼) (comp (fst (iso₂ 𝔼)) (obj (ftor₂ 𝔼) (obj (ftor₁ 𝔼) x))) ▢ arr (ftor₁ 𝔼) (comp (fst (iso₂ 𝔼)) x)
          =⟨ ap (λ m → ⟦ D ⟧ m ▢ arr (ftor₁ 𝔼) (comp (fst (iso₂ 𝔼)) x)) (ap (arr (ftor₁ 𝔼)) (! (iso₂-coher 𝔼 x))) ⟩
        ⟦ D ⟧ arr (ftor₁ 𝔼) (arr (ftor₂ 𝔼) (arr (ftor₁ 𝔼) (comp (fst (iso₂ 𝔼)) x))) ▢ arr (ftor₁ 𝔼) (comp (fst (iso₂ 𝔼)) x) =∎

      zig-zag-swap-<– : (x : ob C) → <–-wc D (snd (iso₁ 𝔼) (obj (ftor₁ 𝔼) x)) == arr (ftor₁ 𝔼) (comp (fst (iso₂ 𝔼)) x)
      zig-zag-swap-<– x = equiv-is-inj (snd (hom-cdom-eqv D (F-equiv-wc (ftor₁ 𝔼 ∘WC ftor₂ 𝔼 ∘WC ftor₁ 𝔼) (snd (iso₂ 𝔼) x)))) _ _ (zig-zag-swap-aux x)

      zig-zag-swap : (x : ob C) → ⟦ D ⟧ comp (fst (iso₁ 𝔼)) (obj (ftor₁ 𝔼) x) ▢ arr (ftor₁ 𝔼) (comp (fst (iso₂ 𝔼)) x) == id₁ D (obj (ftor₁ 𝔼) x)
      zig-zag-swap x =
        ap (λ m → ⟦ D ⟧ comp (fst (iso₁ 𝔼)) (obj (ftor₁ 𝔼) x) ▢ m) (! (zig-zag-swap-<– x)) ∙ ! (<–-wc-rinv D (snd (iso₁ 𝔼) (obj (ftor₁ 𝔼) x)))

      zig-zag-swap-rot : (x : ob C) → arr (ftor₁ 𝔼) (<–-wc C (snd (iso₂ 𝔼) x)) == comp (fst (iso₁ 𝔼)) (obj (ftor₁ 𝔼) x)
      zig-zag-swap-rot x = ap-<–-wc D (! (zig-zag-swap-<– x)) (F-equiv-wc (ftor₁ 𝔼) (snd (iso₂ 𝔼) x)) (equiv-wc-rev D (snd (iso₁ 𝔼) (obj (ftor₁ 𝔼) x)))
