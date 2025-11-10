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

id₁-lft-≃ : ∀ {i j} {C : WildCat {i} {j}} → ∀ {x y} → hom C x y ≃ hom C x y
fst (id₁-lft-≃ {C = C}) f = ⟦ C ⟧ id₁ C _ ▢ f
snd (id₁-lft-≃ {C = C}) = ∼-preserves-equiv (λ x → lamb C x) (idf-is-equiv _)

id₁-rght-≃ : ∀ {i j} {C : WildCat {i} {j}} → ∀ {x y} → hom C x y ≃ hom C x y
fst (id₁-rght-≃ {C = C}) f = ⟦ C ⟧ f ▢ id₁ C _
snd (id₁-rght-≃ {C = C}) = ∼-preserves-equiv (λ x → ρ C x) (idf-is-equiv _)

id₁-comm-reflect-l : ∀ {i j} {C : WildCat {i} {j}} → ∀ {x y} {f₁ f₂ : hom C x y} {p₁ p₂ : f₁ == f₂}
  → ap (λ m → ⟦ C ⟧ id₁ C _ ▢ m) p₁ == ap (λ m → ⟦ C ⟧ id₁ C _ ▢ m) p₂ → p₁ == p₂
id₁-comm-reflect-l {C = C} e = equiv-is-inj (ap-is-equiv (snd (id₁-lft-≃ {C = C})) _ _) _ _ e

id₁-comm-reflect-r : ∀ {i j} {C : WildCat {i} {j}} → ∀ {x y} {f₁ f₂ : hom C x y} {p₁ p₂ : f₁ == f₂}
  → ap (λ m → ⟦ C ⟧ m ▢ id₁ C _) p₁ == ap (λ m → ⟦ C ⟧ m ▢ id₁ C _) p₂ → p₁ == p₂
id₁-comm-reflect-r {C = C} e = equiv-is-inj (ap-is-equiv (snd (id₁-rght-≃ {C = C})) _ _) _ _ e

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

module _ {i j} (C : WildCat {i} {j}) {a b : ob C} where

  equiv-wc-unique : {f : hom C a b} (e₁ e₂ : equiv-wc C f) → <–-wc C e₁ == <–-wc C e₂
  equiv-wc-unique {f} e₁ e₂ = 
    <–-wc C e₁
      =⟨ ρ C (<–-wc C e₁) ⟩
    ⟦ C ⟧ <–-wc C e₁ ▢ id₁ C b
      =⟨ ap (λ m → ⟦ C ⟧ <–-wc C e₁ ▢ m) (<–-wc-rinv C e₂) ⟩
    ⟦ C ⟧ <–-wc C e₁ ▢ ⟦ C ⟧ f ▢ <–-wc C e₂
      =⟨ ! (α C (<–-wc C e₁) f (<–-wc C e₂)) ⟩
    ⟦ C ⟧ (⟦ C ⟧ <–-wc C e₁ ▢  f) ▢ <–-wc C e₂
      =⟨ ap (λ m → ⟦ C ⟧ m ▢  <–-wc C e₂) (! (<–-wc-linv C e₁)) ⟩
    ⟦ C ⟧ id₁ C a ▢  <–-wc C e₂
      =⟨ ! (lamb C (<–-wc C e₂)) ⟩
    <–-wc C e₂ =∎

  ap-<–-wc : {f₁ f₂ : hom C a b} (p : f₁ == f₂)
    (e₁ : equiv-wc C f₁) (e₂ : equiv-wc C f₂) → <–-wc C e₁ == <–-wc C e₂
  ap-<–-wc idp e₁ e₂ = equiv-wc-unique e₁ e₂

Type-wc : (i : ULevel) → WildCat {lsucc i} {i}
ob (Type-wc i) = Type i
hom (Type-wc i) A B = A → B
id₁ (Type-wc i) = idf
_▢_ (Type-wc i) g f = g ∘ f
ρ (Type-wc i) = λ _ → idp
lamb (Type-wc i) = λ _ → idp
α (Type-wc i) = λ _ _ _ → idp

-- triangle identity

triangle-wc : ∀ {i j} (C : WildCat {i} {j}) → Type (lmax i j)
triangle-wc C = {a b c : ob C} (g : hom C b c) (f : hom C a b) → 
  ap (λ m → ⟦ C ⟧ m ▢ f) (ρ C g) ∙
  α C g (id₁ C b) f
    ==
  ap (λ m → ⟦ C ⟧ g ▢ m) (lamb C f)

triangle-wc-ty : ∀ {i} → triangle-wc (Type-wc i)
triangle-wc-ty _ _ = idp

module _ {i j} {C : WildCat {i} {j}} (trig : triangle-wc C)
  {a b c : ob C} (g : hom C b c) (f : hom C a b) where

  abstract

    triangle-wc◃ :
      ap (λ m → ⟦ C ⟧ m ▢ f) (ρ C g) ◃∙
      α C g (id₁ C b) f ◃∎
        =ₛ
      ap (λ m → ⟦ C ⟧ g ▢ m) (lamb C f) ◃∎
    triangle-wc◃ = =ₛ-in (trig g f)

    triangle-wc-rot1 :
      ap (λ m → ⟦ C ⟧ m ▢ f) (ρ C g) ◃∙
      α C g (id₁ C b) f ◃∙
      ! (ap (λ m → ⟦ C ⟧ g ▢ m) (lamb C f)) ◃∎
        =ₛ
      []
    triangle-wc-rot1 = post-rotate'-in triangle-wc◃
    
    triangle-wc-rot2 :
      ap (λ m → ⟦ C ⟧ m ▢ f) (ρ C g) ◃∎
        =ₛ
      ap (λ m → ⟦ C ⟧ g ▢ m) (lamb C f) ◃∙
      ! (α C g (id₁ C b) f) ◃∎
    triangle-wc-rot2 = post-rotate-in triangle-wc◃

-- pentagon identity

pentagon-wc : ∀ {i j} (C : WildCat {i} {j}) → Type (lmax i j)
pentagon-wc C = {a b c d e : ob C} (k : hom C d e) (g : hom C c d) (h : hom C b c) (f : hom C a b) →
  ap (λ m → ⟦ C ⟧ m ▢ f) (α C k g h) ∙ α C k (⟦ C ⟧ g ▢ h) f ∙ ap (λ m → ⟦ C ⟧ k ▢ m) (α C g h f)
    ==
  α C (⟦ C ⟧ k ▢ g) h f ∙ α C k g (⟦ C ⟧ h ▢ f)

pentagon-wc-ty : ∀ {i} → pentagon-wc (Type-wc i)
pentagon-wc-ty _ _ _ _ = idp

module _ {i j} {C : WildCat {i} {j}} (pent : pentagon-wc C)
  {a b c d e : ob C} (k : hom C d e) (g : hom C c d) (h : hom C b c) (f : hom C a b) where

  abstract

    pentagon-wc◃ :
      ap (λ m → ⟦ C ⟧ m ▢ f) (α C k g h) ◃∙ α C k (⟦ C ⟧ g ▢ h) f ◃∙ ap (λ m → ⟦ C ⟧ k ▢ m) (α C g h f) ◃∎
        =ₛ
      α C (⟦ C ⟧ k ▢ g) h f ◃∙ α C k g (⟦ C ⟧ h ▢ f) ◃∎
    pentagon-wc◃ = =ₛ-in (pent k g h f)

    pentagon-wc-! :
      ! (ap (λ m → ⟦ C ⟧ k ▢ m) (α C g h f)) ◃∙ ! (α C k (⟦ C ⟧ g ▢ h) f) ◃∙ ! (ap (λ m → ⟦ C ⟧ m ▢ f) (α C k g h)) ◃∎ 
        =ₛ
      ! (α C k g (⟦ C ⟧ h ▢ f)) ◃∙ ! (α C (⟦ C ⟧ k ▢ g) h f) ◃∎
    pentagon-wc-! = !-=ₛ pentagon-wc◃

    pentagon-wc-!-rot1 :
      α C k g (⟦ C ⟧ h ▢ f) ◃∙ ! (ap (λ m → ⟦ C ⟧ k ▢ m) (α C g h f)) ◃∙ ! (α C k (⟦ C ⟧ g ▢ h) f) ◃∙ ! (ap (λ m → ⟦ C ⟧ m ▢ f) (α C k g h)) ◃∎ 
        =ₛ
      ! (α C (⟦ C ⟧ k ▢ g) h f) ◃∎
    pentagon-wc-!-rot1 = pre-rotate-out pentagon-wc-!

    pentagon-wc-rot1 : 
      ! (α C (⟦ C ⟧ k ▢ g) h f) ◃∙ ap (λ m → ⟦ C ⟧ m ▢ f) (α C k g h) ◃∙ α C k (⟦ C ⟧ g ▢ h) f ◃∎
        =ₛ
      α C k g (⟦ C ⟧ h ▢ f) ◃∙ ! (ap (λ m → ⟦ C ⟧ k ▢ m) (α C g h f)) ◃∎
    pentagon-wc-rot1 = post-rotate-in (pre-rotate'-in pentagon-wc◃)

    pentagon-wc-rot2 : 
      ! (α C k (⟦ C ⟧ g ▢ h) f) ◃∙ ap (λ m → ⟦ C ⟧ m ▢ f) (! (α C k g h)) ◃∙ α C (⟦ C ⟧ k ▢ g) h f ◃∎
        =ₛ
      ap (λ m → ⟦ C ⟧ k ▢ m) (α C g h f) ◃∙ ! (α C k g (⟦ C ⟧ h ▢ f)) ◃∎
    pentagon-wc-rot2 = 
      ! (α C k (⟦ C ⟧ g ▢ h) f) ◃∙ ap (λ m → ⟦ C ⟧ m ▢ f) (! (α C k g h)) ◃∙ α C (⟦ C ⟧ k ▢ g) h f ◃∎
        =ₛ₁⟨ 1 & 1 & ap-! (λ m → ⟦ C ⟧ m ▢ f) (α C k g h) ⟩
      ! (α C k (⟦ C ⟧ g ▢ h) f) ◃∙ ! (ap (λ m → ⟦ C ⟧ m ▢ f) (α C k g h)) ◃∙ α C (⟦ C ⟧ k ▢ g) h f ◃∎
        =ₛ₁⟨ 2 & 1 & ! (!-! _) ⟩
      ! (α C k (⟦ C ⟧ g ▢ h) f) ◃∙ ! (ap (λ m → ⟦ C ⟧ m ▢ f) (α C k g h)) ◃∙ ! (! (α C (⟦ C ⟧ k ▢ g) h f)) ◃∎
        =ₛ⟨ !-=ₛ pentagon-wc-rot1 ⟩
      ! (! (ap (λ m → ⟦ C ⟧ k ▢ m) (α C g h f))) ◃∙ ! (α C k g (⟦ C ⟧ h ▢ f)) ◃∎
        =ₛ₁⟨ 0 & 1 & !-! _ ⟩
      ap (λ m → ⟦ C ⟧ k ▢ m) (α C g h f) ◃∙ ! (α C k g (⟦ C ⟧ h ▢ f)) ◃∎ ∎ₛ

    pentagon-wc-rot3 :
      ap (λ m → ⟦ C ⟧ k ▢ m) (α C g h f) ◃∎
          =ₛ
      ! (α C k (⟦ C ⟧ g ▢ h) f) ◃∙ ap (λ m → ⟦ C ⟧ m ▢ f) (! (α C k g h)) ◃∙ α C (⟦ C ⟧ k ▢ g) h f ◃∙ α C k g (⟦ C ⟧ h ▢ f) ◃∎
    pentagon-wc-rot3 = pre-rotate-in (pre-rotate-in pentagon-wc◃) ∙ₛ aux
      where abstract
        aux :
          ! (α C k (⟦ C ⟧ g ▢ h) f) ◃∙ ! (ap (λ m → ⟦ C ⟧ m ▢ f) (α C k g h)) ◃∙ α C (⟦ C ⟧ k ▢ g) h f ◃∙ α C k g (⟦ C ⟧ h ▢ f) ◃∎
            =ₛ
          ! (α C k (⟦ C ⟧ g ▢ h) f) ◃∙ ap (λ m → ⟦ C ⟧ m ▢ f) (! (α C k g h)) ◃∙ α C (⟦ C ⟧ k ▢ g) h f ◃∙ α C k g (⟦ C ⟧ h ▢ f) ◃∎
        aux =
          ! (α C k (⟦ C ⟧ g ▢ h) f) ◃∙ ! (ap (λ m → ⟦ C ⟧ m ▢ f) (α C k g h)) ◃∙ α C (⟦ C ⟧ k ▢ g) h f ◃∙ α C k g (⟦ C ⟧ h ▢ f) ◃∎
            =ₛ₁⟨ 1 & 1 & !-ap (λ m → ⟦ C ⟧ m ▢ f) (α C k g h) ⟩
          ! (α C k (⟦ C ⟧ g ▢ h) f) ◃∙ ap (λ m → ⟦ C ⟧ m ▢ f) (! (α C k g h)) ◃∙ α C (⟦ C ⟧ k ▢ g) h f ◃∙ α C k g (⟦ C ⟧ h ▢ f) ◃∎ ∎ₛ

    pentagon-wc-rot4 :
      ! (α C (⟦ C ⟧ k ▢ g) h f) ◃∙ ap (λ m → ⟦ C ⟧ m ▢ f) (α C k g h) ◃∙ α C k (⟦ C ⟧ g ▢ h) f ◃∙ ap (λ m → ⟦ C ⟧ k ▢ m) (α C g h f) ◃∎
        =ₛ
      α C k g (⟦ C ⟧ h ▢ f) ◃∎
    pentagon-wc-rot4 = pre-rotate'-in pentagon-wc◃ 
