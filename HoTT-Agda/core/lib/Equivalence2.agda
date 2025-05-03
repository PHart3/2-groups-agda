{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Paths
open import lib.types.Unit
open import lib.types.Empty
open import lib.FTID

module lib.Equivalence2 where

{- Pre- and post- composition with equivalences are equivalences -}
module _ {i j k} {A : Type i} {B : Type j} {C : Type k}
         {h : A → B} (e : is-equiv h) where

  pre∘-is-equiv : is-equiv (λ (k : B → C) → k ∘ h)
  pre∘-is-equiv = is-eq f g f-g g-f
    where f = _∘ h
          g = _∘ is-equiv.g e
          f-g = λ k → ap (k ∘_) (λ= $ is-equiv.g-f e)
          g-f = λ k → ap (k ∘_) (λ= $ is-equiv.f-g e)

  post∘-is-equiv : is-equiv (λ (k : C → A) → h ∘ k)
  post∘-is-equiv = is-eq f g f-g g-f
    where f = h ∘_
          g = is-equiv.g e ∘_
          f-g = λ k → ap (_∘ k) (λ= $ is-equiv.f-g e)
          g-f = λ k → ap (_∘ k) (λ= $ is-equiv.g-f e)

{- The same thing on the abstraction level of equivalences -}
module _ {i j k} {A : Type i} {B : Type j} {C : Type k}
         (e : A ≃ B) where

  pre∘-equiv : (B → C) ≃ (A → C)
  pre∘-equiv = (_ , pre∘-is-equiv (snd e))

  post∘-equiv : (C → A) ≃ (C → B)
  post∘-equiv = (_ , post∘-is-equiv (snd e))

is-contr-map : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) → Type (lmax i j)
is-contr-map {A = A} {B = B} f = (y : B) → is-contr (hfiber f y)

equiv-is-contr-map : ∀ {i j} {A : Type i} {B : Type j} {f : A → B}
  → (is-equiv f → is-contr-map f)
equiv-is-contr-map e y =
   equiv-preserves-level (Σ-emap-l (_== y) (_ , e) ⁻¹)

contr-map-is-equiv : ∀ {i j} {A : Type i} {B : Type j} {f : A → B}
  → (is-contr-map f → is-equiv f)
contr-map-is-equiv {f = f} cm = is-eq _
  (λ b → fst (contr-center (cm b)))
  (λ b → snd (contr-center (cm b)))
  (λ a → ap fst (contr-path (cm (f a)) (a , idp)))

fiber=-econv : ∀ {i j} {A : Type i} {B : Type j} {h : A → B} {y : B}
  (r s : Σ A (λ x → h x == y))
  → (r == s) ≃ Σ (fst r == fst s) (λ γ → ap h γ ∙ snd s == snd r)
fiber=-econv r s = Σ-emap-r (λ γ → !-equiv ∘e (↓-app=cst-econv ⁻¹)) ∘e ((=Σ-econv r s)⁻¹)

module _ {i j} {A : Type i} {B : Type j} where

  linv : (A → B) → Type (lmax i j)
  linv f = Σ (B → A) (λ g → (∀ x → g (f x) == x))

  rinv : (A → B) → Type (lmax i j)
  rinv f = Σ (B → A) (λ g → (∀ y → f (g y) == y))

  bi-inv : (A → B) → Type (lmax i j)
  bi-inv f = rinv f × linv f

  bi-inv-eqv : {f : A → B} → bi-inv f → is-equiv f
  bi-inv-eqv {f} ((g , α) , (h , β)) =
    is-eq f g α (λ a → ! (β (g (f a))) ∙ ap h (α (f a)) ∙ β a)

  lcoh : (f : A → B) → linv f → Type (lmax i j)
  lcoh f (g , g-f) = Σ (∀ y → f (g y) == y)
                       (λ f-g → ∀ y → ap g (f-g y) == g-f (g y))

  rcoh : (f : A → B) → rinv f → Type (lmax i j)
  rcoh f (g , f-g) = Σ (∀ x → g (f x) == x)
                       (λ g-f → ∀ x → ap f (g-f x) == f-g (f x))

  module _ {k} {C : Type k} {f : A → B} where

    cmp-eqv-linv : (g : B → C) → is-equiv (g ∘ f) → linv f
    fst (cmp-eqv-linv g e) = is-equiv.g e ∘ g
    snd (cmp-eqv-linv g e) = is-equiv.g-f e

    cmp-eqv-rinv : (g : C → A) → is-equiv (f ∘ g) → rinv f
    fst (cmp-eqv-rinv g e) = g ∘ is-equiv.g e
    snd (cmp-eqv-rinv g e) = is-equiv.f-g e

module _ {i j} {A : Type i} {B : Type j} {f : A → B} (e : is-equiv f) where

  equiv-linv-is-contr : is-contr (linv f)
  equiv-linv-is-contr = equiv-preserves-level (Σ-emap-r λ _ → λ=-equiv ⁻¹)
                          {{equiv-is-contr-map (pre∘-is-equiv e) (idf A)}}

  equiv-rinv-is-contr : is-contr (rinv f)
  equiv-rinv-is-contr = equiv-preserves-level (Σ-emap-r λ _ → λ=-equiv ⁻¹)
                          {{equiv-is-contr-map (post∘-is-equiv e) (idf B)}}

module _ {i j} {A : Type i} {B : Type j} {f : A → B} where

  rcoh-econv : (v : rinv f)
    → rcoh f v ≃ Π A (λ x → (fst v (f x) , snd v (f x)) == (x , idp {a = f x}))
  rcoh-econv v = Π-emap-r (λ x → ((fiber=-econv {h = f} _ _)⁻¹) ∘e apply-unit-r x) ∘e choice ⁻¹
    where
      apply-unit-r : ∀ x → Σ _ (λ γ → ap f γ == _) ≃ Σ _ (λ γ → ap f γ ∙ idp == _)
      apply-unit-r x = Σ-emap-r λ γ
        → coe-equiv (ap (λ q → q == snd v (f x)) (! (∙-unit-r _)))

  lcoh-econv : (v : linv f)
    → lcoh f v ≃ Π B (λ y → (f (fst v y) , snd v (fst v y)) == (y , idp))
  lcoh-econv v = Π-emap-r (λ y → ((fiber=-econv {h = fst v} _ _)⁻¹) ∘e apply-unit-r y) ∘e choice ⁻¹
    where
      apply-unit-r : ∀ y → Σ _ (λ γ → ap (fst v) γ == _) ≃ Σ _ (λ γ → ap (fst v) γ ∙ idp == _)
      apply-unit-r y = Σ-emap-r λ γ
        → coe-equiv (ap (λ q → q == snd v (fst v y)) (! (∙-unit-r _)))

equiv-rcoh-is-contr : ∀ {i j} {A : Type i} {B : Type j} {f : A → B}
                      (e : is-equiv f) → (v : rinv f) → is-contr (rcoh f v)
equiv-rcoh-is-contr {f = f} e v = equiv-preserves-level ((rcoh-econv v)⁻¹)
  {{Π-level (λ x → =-preserves-level (equiv-is-contr-map e (f x)))}}

rinv-and-rcoh-is-equiv : ∀ {i j} {A : Type i} {B : Type j} {h : A → B}
  → Σ (rinv h) (rcoh h) ≃ is-equiv h
rinv-and-rcoh-is-equiv {h = h} = equiv f g (λ _ → idp) (λ _ → idp)
  where f : Σ (rinv h) (rcoh h) → is-equiv h
        f s = record {g = fst (fst s); f-g = snd (fst s);
                      g-f = fst (snd s); adj = snd (snd s)}
        g : is-equiv h → Σ (rinv h) (rcoh h)
        g t = ((is-equiv.g t , is-equiv.f-g t) , (is-equiv.g-f t , is-equiv.adj t))

abstract
  is-equiv-is-prop : ∀ {i j} {A : Type i} {B : Type j} {f : A → B}
    → is-prop (is-equiv f)
  is-equiv-is-prop = inhab-to-contr-is-prop λ e →
    equiv-preserves-level rinv-and-rcoh-is-equiv
      {{Σ-level (equiv-rinv-is-contr e) (equiv-rcoh-is-contr e)}}

  instance
    is-equiv-level : ∀ {i j} {A : Type i} {B : Type j} {f : A → B} {n : ℕ₋₂}
      → has-level (S n) (is-equiv f)
    is-equiv-level = prop-has-level-S is-equiv-is-prop

is-equiv-prop : ∀ {i j} {A : Type i} {B : Type j}
  → SubtypeProp {A = A → B} {lmax i j}
is-equiv-prop = subtypeprop is-equiv {{λ {f} → is-equiv-is-prop}}

∘e-unit-r : ∀ {i} {A B : Type i} (e : A ≃ B) → (e ∘e ide A) == e
∘e-unit-r e = pair= idp (prop-has-all-paths _ _)

-- 3-for-2
3-for-2-e : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} {f₀ : A → B} {f₁ : B → C}
  (f₂ : A → C) → f₁ ∘ f₀ ∼ f₂ → is-equiv f₀ → is-equiv f₂ → is-equiv f₁
3-for-2-e {f₀ = f₀} {f₁ = f₁} =
  ∼-ind (λ f₂ _ → is-equiv f₀ → is-equiv f₂ → is-equiv f₁)
    λ e₀ e₁ → ∼-preserves-equiv {f₀ = f₁ ∘ f₀ ∘ is-equiv.g e₀} (λ x → ap f₁ (is-equiv.f-g e₀ x)) (e₁ ∘ise is-equiv-inverse e₀) 

equiv-induction-bi : ∀ {i j}
  (P : {A B C : Type i} (f₁ : A ≃ B) (f₂ : B ≃ C) → Type j)
  (d : (A : Type i) → P (ide A) (ide A))
  → {A B C : Type i} (f₁ : A ≃ B) (f₂ : B ≃ C)
  → P f₁ f₂
equiv-induction-bi {i} {j} P d f₁ f₂ =
  transp2 P (coe-equiv-β f₁) (coe-equiv-β f₂)
    (aux P d (ua f₁) (ua f₂))
  where
    aux : (P : {A B C : Type i} (f₁ : A ≃ B) (f₂ : B ≃ C) → Type j)
      (d : (A : Type i) → P (ide A) (ide A))
      {A B C : Type i} (p₁ : A == B) (p₂ : B == C)
      → P (coe-equiv p₁) (coe-equiv p₂)
    aux P d idp idp = d _

equiv-induction-tri : ∀ {i j}
  (P : {A B C D : Type i} (f₁ : A ≃ B) (f₂ : B ≃ C) (f₃ : C ≃ D) → Type j)
  (d : (A : Type i) → P (ide A) (ide A) (ide A))
  → {A B C D : Type i} (f₁ : A ≃ B) (f₂ : B ≃ C) (f₃ : C ≃ D)
  → P f₁ f₂ f₃
equiv-induction-tri {i} {j} P d f₁ f₂ f₃ =
  transp3 P (coe-equiv-β f₁) (coe-equiv-β f₂) (coe-equiv-β f₃)
    (aux P d (ua f₁) (ua f₂) (ua f₃))
  where
    aux : (P : {A B C D : Type i} (f₁ : A ≃ B) (f₂ : B ≃ C) (f₃ : C ≃ D) → Type j)
      (d : (A : Type i) → P (ide A) (ide A) (ide A))
      {A B C D : Type i} (p₁ : A == B) (p₂ : B == C) (p₃ : C == D)
      → P (coe-equiv p₁) (coe-equiv p₂) (coe-equiv p₃)
    aux P d idp idp idp = d _

ua-∘e : ∀ {i} {C A B : Type i} (e₁ : A ≃ B) (e₂ : B ≃ C)
  → ua (e₂ ∘e e₁) == ua e₁ ∙ ua e₂
ua-∘e {C = C} =
  equiv-induction-b
    (λ {B} e₁ → ∀ (e₂ : B ≃ C) → ua (e₂ ∘e e₁) == ua e₁ ∙ ua e₂)
    (λ e₂ → ap ua (∘e-unit-r e₂) ∙ ap (λ w → (w ∙ ua e₂)) (! (ua-η idp)))

ua-∘e-β : ∀ {i} {A C : Type i} (e : A ≃ C)
  → ua-∘e (ide A) e == ap ua (∘e-unit-r e) ∙ ap (λ w → (w ∙ ua e)) (! (ua-η idp))
ua-∘e-β {C = C} e =
  app= (equiv-induction-β {P = λ {B} e₁ → ∀ (e₂ : B ≃ C) → ua (e₂ ∘e e₁) == ua e₁ ∙ ua e₂} _) e 

ua-∘e-coh : ∀ {i} {C A B : Type i} (e₂ : B ≃ C) {e₁ e₁' : A ≃ B} (p : e₁ == e₁')
  →
  ua-∘e e₁ e₂ ◃∎
    =ₛ
  ap ua (ap (λ e → e₂ ∘e e) p) ◃∙
  ua-∘e e₁' e₂ ◃∙
  ! (ap (λ q → q ∙ ua e₂) (ap ua p)) ◃∎
ua-∘e-coh e₂ {e₁ = e₁} idp = =ₛ-in (! (∙-unit-r (ua-∘e e₁ e₂)))

∙-coe-equiv : ∀ {i} {A B C : Type i} (p₁ : A == B) (p₂ : B == C)
  → coe-equiv p₂ ∘e coe-equiv p₁ == coe-equiv (p₁ ∙ p₂)
∙-coe-equiv idp p₂ = ∘e-unit-r (coe-equiv p₂)

postulate  -- rest of univalence axiom
  ua-adj : ∀ {i} {A B : Type i} (p : A == B) → ap coe-equiv (ua-η p) == coe-equiv-β (coe-equiv p)

coe-β-∘ : ∀ {i} {A B C : Type i} (h₁ : A ≃ C) (h₂ : C ≃ B)
  {e : A ≃ B} (H : e == h₂ ∘e h₁) (x : A)
  →
  coe-β e x ◃∎
    =ₛ
  app= (ap coe (ap ua H)) x ◃∙
  app= (ap coe (ua-∘e h₁ h₂)) x ◃∙
  coe-∙ (ua h₁) (ua h₂) x ◃∙
  ap (coe (ua h₂)) (coe-β h₁ x) ◃∙
  coe-β h₂ (–> h₁ x) ◃∙
  ! (app= (ap –> H) x) ◃∎
coe-β-∘ h₁ h₂ idp = 
  equiv-induction-bi
    (λ k₁ k₂ → (x : _) → 
      coe-β (k₂ ∘e k₁) x ◃∎
        =ₛ
      idp ◃∙
      app= (ap coe (ua-∘e k₁ k₂)) x ◃∙
      coe-∙ (ua k₁) (ua k₂) x ◃∙
      ap (coe (ua k₂)) (coe-β k₁ x) ◃∙
      coe-β k₂ (–> k₁ x) ◃∙
      idp ◃∎)
       (λ A x → !ₛ (aux x)) h₁ h₂
  where
    aux : ∀ {i} {A : Type i} (x : A) →
      idp ◃∙
      app= (ap coe (ua-∘e (ide A) (ide A))) x ◃∙
      coe-∙ (ua (ide A)) (ua (ide A)) x ◃∙
      ap (coe (ua (ide A))) (coe-β (ide A) x) ◃∙
      coe-β (ide A) x ◃∙
      idp ◃∎
        =ₛ
      coe-β (ide A ∘e ide A) x ◃∎
    aux {A = A} x = 
      idp ◃∙
      app= (ap coe (ua-∘e (ide A) (ide A))) x ◃∙
      coe-∙ (ua (ide A)) (ua (ide A)) x ◃∙
      ap (coe (ua (ide A))) (coe-β (ide A) x) ◃∙
      coe-β (ide A) x ◃∙
      idp ◃∎
        =ₛ₁⟨ 0 & 2 & ap (λ p → app= (ap coe p) x) (ua-∘e-β (ide A)) ⟩
      app= (ap coe
        (ap ua (∘e-unit-r (ide A)) ∙
        ap (λ w → w ∙ ua (ide A)) (! (ua-η idp)))) x ◃∙
      coe-∙ (ua (ide A)) (ua (ide A)) x ◃∙
      ap (coe (ua (ide A))) (coe-β (ide A) x) ◃∙
      coe-β (ide A) x ◃∙
      idp ◃∎
        =ₛ₁⟨ 2 & 1 & ap (ap (coe (ua (ide A)))) (ap (ap (λ e → –> e x)) (! (ua-adj idp))) ⟩
      app= (ap coe
        (ap ua (∘e-unit-r (ide A)) ∙
        ap (λ w → w ∙ ua (ide A)) (! (ua-η idp)))) x ◃∙
      coe-∙ (ua (ide A)) (ua (ide A)) x ◃∙
      ap (coe (ua (ide A))) (ap (λ e → –> e x) (ap coe-equiv (ua-η idp))) ◃∙
      coe-β (ide A) x ◃∙
      idp ◃∎
        =ₛ₁⟨ 3 & 2 & ∙-unit-r (coe-β (ide A) x) ⟩
      app= (ap coe
        (ap ua (∘e-unit-r (ide A)) ∙
        ap (λ w → w ∙ ua (ide A)) (! (ua-η idp)))) x ◃∙
      coe-∙ (ua (ide A)) (ua (ide A)) x ◃∙
      ap (coe (ua (ide A))) (ap (λ e → –> e x) (ap coe-equiv (ua-η idp))) ◃∙
      coe-β (ide A) x ◃∎
        =ₛ⟨ =ₛ-in (aux-path (∘e-unit-r (ide A)) (coe-β (ide A) x)) ⟩
      ap (λ z → coe (ua z) x) (∘e-unit-r (ide A)) ◃∙
      coe-β (ide A) x ◃∙
      idp ◃∎
        =ₛ₁⟨ 2 & 1 &
          ap ! (! (ap-∘ (λ k → k x) fst (∘e-unit-r (ide A)) ∙
            ap (ap (λ k → k x)) (fst=-β idp _))) ⟩
      ap (λ z → coe (ua z) x) (∘e-unit-r (ide A)) ◃∙
      coe-β (ide A) x ◃∙
      ! (ap (λ z → –> z x) (∘e-unit-r (ide A))) ◃∎
        =ₛ⟨ !ₛ (apCommSq2◃' (λ z → coe-β z x) (∘e-unit-r (ide A)) ) ⟩
      coe-β (ide A ∘e ide A) x ◃∎ ∎ₛ
      where
        aux-path : {a : A} {e : A ≃ A} (p₁ : e == ide A) (p₂ : _ == a) → 
          app= (ap coe (ap ua p₁ ∙
            ap (λ w → w ∙ ua (ide A)) (! (ua-η idp)))) x ∙
          coe-∙ (ua (ide A)) (ua (ide A)) x ∙
          ap (coe (ua (ide A))) (ap (λ e → –> e x) (ap coe-equiv (ua-η idp))) ∙
          p₂
            ==
          ap (λ z → coe (ua z) x) p₁ ∙
          p₂ ∙ idp
        aux-path idp idp = aux-path-aux (ua-η idp)
          where
            aux-path-aux : {r : A == A} (p : r == idp) → 
              app= (ap coe (ap (λ w → w ∙ r) (! p))) x ∙
              coe-∙ r r x ∙
              ap (coe r) (ap (λ e → –> e x) (ap coe-equiv p)) ∙ idp
                ==
              idp
            aux-path-aux idp = idp
          
ap-ua-∘e : ∀ {i} {C A B : Type i} (e₁ : A ≃ B) (e₂ : B ≃ C)
  →
  ap coe-equiv (ua-∘e e₁ e₂) ◃∎
    =ₛ
  coe-equiv-β (e₂ ∘e e₁) ◃∙
  ap2 _∘e_ (! (coe-equiv-β e₂)) (! (coe-equiv-β e₁)) ◃∙
  ∙-coe-equiv (ua e₁) (ua e₂) ◃∎  
ap-ua-∘e {C = C} {A} = 
  equiv-induction-b
    (λ {B} e₁ → ∀ (e₂ : B ≃ C) →
      ap coe-equiv (ua-∘e e₁ e₂) ◃∎
        =ₛ
      coe-equiv-β (e₂ ∘e e₁) ◃∙
      ap2 _∘e_ (! (coe-equiv-β e₂)) (! (coe-equiv-β e₁)) ◃∙
      ∙-coe-equiv (ua e₁) (ua e₂) ◃∎)
    aux
  where
    open is-equiv
    aux2 : (e₂ : A ≃ C) →
      ap2 _∘e_ (! (coe-equiv-β e₂)) (! (coe-equiv-β (ide A))) ◃∙
      ap (λ z → coe-equiv (ua e₂) ∘e coe-equiv z) (ua-η idp) ◃∙
      ∘e-unit-r (coe-equiv (ua e₂)) ◃∎
        =ₛ
      ap (λ z → z) (∘e-unit-r e₂) ◃∙
      ! (coe-equiv-β e₂) ◃∎
    aux2 e₂ = 
      ap2 _∘e_ (! (coe-equiv-β e₂)) (! (coe-equiv-β (ide A))) ◃∙
      ap (λ z → coe-equiv (ua e₂) ∘e coe-equiv z) (ua-η idp) ◃∙
      ∘e-unit-r (coe-equiv (ua e₂)) ◃∎
        =ₛ⟨ 0 & 1 & ap2-out _∘e_ (! (coe-equiv-β e₂)) (! (coe-equiv-β (ide A))) ⟩
      ap (λ u → u ∘e ide A) (! (coe-equiv-β e₂)) ◃∙
      ap (_∘e_ (coe-equiv (ua e₂))) (! (coe-equiv-β (ide A))) ◃∙
      ap (λ z → coe-equiv (ua e₂) ∘e coe-equiv z) (ua-η idp) ◃∙
      ∘e-unit-r (coe-equiv (ua e₂)) ◃∎
        =ₛ₁⟨ 2 & 1 & ap-∘ (_∘e_ (coe-equiv (ua e₂))) coe-equiv (ua-η idp) ⟩
      ap (λ u → u ∘e ide A) (! (coe-equiv-β e₂)) ◃∙
      ap (_∘e_ (coe-equiv (ua e₂))) (! (coe-equiv-β (ide A))) ◃∙
      ap (_∘e_ (coe-equiv (ua e₂))) (ap coe-equiv (ua-η idp)) ◃∙
      ∘e-unit-r (coe-equiv (ua e₂)) ◃∎
        =ₛ⟨ 1 & 2 & ∙-ap◃ (_∘e_ (coe-equiv (ua e₂))) (! (coe-equiv-β (ide A))) (ap coe-equiv (ua-η idp)) ⟩
      ap (λ u → u ∘e ide A) (! (coe-equiv-β e₂)) ◃∙
      ap (_∘e_ (coe-equiv (ua e₂))) (! (coe-equiv-β (ide A)) ∙ ap coe-equiv (ua-η idp)) ◃∙
      ∘e-unit-r (coe-equiv (ua e₂)) ◃∎
        =ₛ₁⟨ 1 & 1 &
          ap (λ p → ap (_∘e_ (coe-equiv (ua e₂))) (! (coe-equiv-β (ide A)) ∙ p)) (ua-adj idp) ∙
          ap (ap (_∘e_ (coe-equiv (ua e₂)))) (!-inv-l (coe-equiv-β (ide A))) ⟩
      ap (λ u → u ∘e ide A) (! (coe-equiv-β e₂)) ◃∙
      idp ◃∙
      ∘e-unit-r (coe-equiv (ua e₂)) ◃∎
        =ₛ⟨ 2 & 1 & apCommSq2◃' ∘e-unit-r (coe-equiv-β e₂) ⟩
      ap (λ z → z ∘e ide A) (! (coe-equiv-β e₂)) ◃∙
      idp ◃∙
      ap (λ z → z ∘e ide A) (coe-equiv-β e₂) ◃∙
      ∘e-unit-r e₂ ◃∙
      ! (ap (λ z → z) (coe-equiv-β e₂)) ◃∎
        =ₛ₁⟨ 0 & 1 & ap-! (λ z → z ∘e ide A) (coe-equiv-β e₂) ⟩
      _
        =ₛ₁⟨ 0 & 3 & !-inv-l (ap (λ z → z ∘e ide A) (coe-equiv-β e₂)) ⟩
      idp ◃∙
      ∘e-unit-r e₂ ◃∙
      ! (ap (λ z → z) (coe-equiv-β e₂)) ◃∎
        =ₛ₁⟨ 0 & 2 & ! (ap-idf (∘e-unit-r e₂)) ⟩
      _
        =ₛ₁⟨ 1 & 1 & ap ! (ap-idf (coe-equiv-β e₂)) ⟩
      ap (λ z → z) (∘e-unit-r e₂) ◃∙
      ! (coe-equiv-β e₂) ◃∎ ∎ₛ

    aux : (e₂ : A ≃ C) →
      ap coe-equiv (ua-∘e (ide A) e₂) ◃∎
        =ₛ
      coe-equiv-β (e₂ ∘e ide A) ◃∙
      ap2 _∘e_ (! (coe-equiv-β e₂)) (! (coe-equiv-β (ide A))) ◃∙
      ∙-coe-equiv (ua (ide A)) (ua e₂) ◃∎
    aux e₂ =
      ap coe-equiv (ua-∘e (ide A) e₂) ◃∎
        =ₛ₁⟨ ap (ap coe-equiv) (ua-∘e-β e₂) ⟩
      ap coe-equiv (ap ua (∘e-unit-r e₂) ∙ ap (λ w → w ∙ ua e₂) (! (ua-η idp))) ◃∎
        =ₛ⟨ !ₛ (∙-ap◃ coe-equiv (ap ua (∘e-unit-r e₂)) (ap (λ w → w ∙ ua e₂) (! (ua-η idp)))) ⟩
      ap coe-equiv (ap ua (∘e-unit-r e₂)) ◃∙
      ap coe-equiv (ap (λ w → w ∙ ua e₂) (! (ua-η idp))) ◃∎
        =ₛ₁⟨ 0 & 1 & ∘-ap coe-equiv ua (∘e-unit-r e₂) ⟩
      ap (coe-equiv ∘ ua) (∘e-unit-r e₂) ◃∙
      ap coe-equiv (ap (λ w → w ∙ ua e₂) (! (ua-η idp))) ◃∎
        =ₛ⟨ 0 & 1 & hmtpy-nat-∙◃ coe-equiv-β (∘e-unit-r e₂) ⟩
      coe-equiv-β (e₂ ∘e ide A) ◃∙
      ap (λ z → z) (∘e-unit-r e₂) ◃∙
      ! (coe-equiv-β e₂) ◃∙
      ap coe-equiv (ap (λ w → w ∙ ua e₂) (! (ua-η idp))) ◃∎
        =ₛ₁⟨ 3 & 1 & 
          ap (ap coe-equiv) (ap-! (λ w → w ∙ ua e₂) (ua-η idp)) ∙
          ap-! coe-equiv (ap (λ w → w ∙ ua e₂) (ua-η idp)) ∙
          ap ! (∘-ap coe-equiv (λ w → w ∙ ua e₂) (ua-η idp)) ⟩
      coe-equiv-β (e₂ ∘e ide A) ◃∙
      ap (λ z → z) (∘e-unit-r e₂) ◃∙
      ! (coe-equiv-β e₂) ◃∙
      ! (ap (λ z → coe-equiv (z ∙ ua e₂)) (ua-η idp)) ◃∎
        =ₛ⟨ 1 & 2 & !ₛ (aux2 e₂) ⟩
      coe-equiv-β (e₂ ∘e ide A) ◃∙
      ap2 _∘e_ (! (coe-equiv-β e₂)) (! (coe-equiv-β (ide A))) ◃∙
      ap (λ z → coe-equiv (ua e₂) ∘e coe-equiv z) (ua-η idp) ◃∙
      ∘e-unit-r (coe-equiv (ua e₂)) ◃∙
      ! (ap (λ z → coe-equiv (z ∙ ua e₂)) (ua-η idp)) ◃∎
        =ₛ⟨ 2 & 3 & !ₛ (apCommSq2◃' (λ z → ∙-coe-equiv z (ua e₂)) (ua-η idp)) ⟩
      coe-equiv-β (e₂ ∘e ide A) ◃∙
      ap2 _∘e_ (! (coe-equiv-β e₂)) (! (coe-equiv-β (ide A))) ◃∙
      ∙-coe-equiv (ua (ide A)) (ua e₂) ◃∎ ∎ₛ

{- Adjointion where hom = path -}

module _ {i j} {A : Type i} {B : Type j} (e : A ≃ B) where

  equiv-adj : ∀ {a b} → (–> e a == b) → (a == <– e b)
  equiv-adj p = ! (<–-inv-l e _) ∙ ap (<– e) p

  equiv-adj' : ∀ {a b} → (a == <– e b) → (–> e a == b)
  equiv-adj' p = ap (–> e) p ∙ (<–-inv-r e _)

{- Type former equivalences involving Empty may require λ=. -}
module _ {j} {B : Empty → Type j} where
  Σ₁-Empty : Σ Empty B ≃ Empty
  Σ₁-Empty = equiv (⊥-rec ∘ fst) ⊥-rec ⊥-elim (⊥-rec ∘ fst)

  Π₁-Empty : Π Empty B ≃ Unit
  Π₁-Empty = equiv (cst tt) (cst ⊥-elim) (λ _ → contr-has-all-paths _ _) (λ _ → λ= ⊥-elim)

Σ₂-Empty : ∀ {i} {A : Type i} → Σ A (λ _ → Empty) ≃ Empty
Σ₂-Empty = equiv (⊥-rec ∘ snd) ⊥-rec ⊥-elim (⊥-rec ∘ snd)

{- Fiberwise equivalence -}
module _ {i j k} {A : Type i} {P : A → Type j} {Q : A → Type k}
  (f : ∀ x → P x → Q x) where

  private
    f-tot : Σ A P → Σ A Q
    f-tot = Σ-fmap-r f

  fiber-equiv-is-total-equiv : (∀ x → is-equiv (f x)) → is-equiv f-tot
  fiber-equiv-is-total-equiv f-ise = is-eq _ from to-from from-to
    where
      from : Σ A Q → Σ A P
      from (x , y) = x , is-equiv.g (f-ise x) y

      abstract
        to-from : ∀ q → f-tot (from q) == q
        to-from (x , q) = pair= idp (is-equiv.f-g (f-ise x) q)

        from-to : ∀ p → from (f-tot p) == p
        from-to (x , p) = pair= idp (is-equiv.g-f (f-ise x) p)

  total-equiv-is-fiber-equiv : is-equiv f-tot → (∀ x → is-equiv (f x))
  total-equiv-is-fiber-equiv f-tot-ise x = is-eq _ from to-from from-to
    where
      module f-tot = is-equiv f-tot-ise

      from : Q x → P x
      from q = transport P (fst= (f-tot.f-g (x , q))) (snd (f-tot.g (x , q)))

      abstract
        from-lemma : ∀ q → snd (f-tot.g (x , q)) == from q
          [ P ↓ fst= (f-tot.f-g (x , q)) ]
        from-lemma q = from-transp P (fst= (f-tot.f-g (x , q))) idp

        to-from : ∀ q → f x (from q) == q
        to-from q =
          transport (λ path → f x (from q) == q [ Q ↓ path ])
            (!-inv-l (fst= (f-tot.f-g (x , q))))
            (!ᵈ (ap↓ (λ {x} → f x) (from-lemma q)) ∙ᵈ snd= (f-tot.f-g (x , q)))

        from-to : ∀ p → from (f x p) == p
        from-to p =
          transport (λ path → from (f x p) == p [ P ↓ path ])
            ( ap (λ path → ! path ∙ fst= (f-tot.g-f (x , p)))
                (ap fst= (! (f-tot.adj (x , p))) ∙ ∘-ap fst f-tot (f-tot.g-f (x , p)))
            ∙ !-inv-l (fst= (f-tot.g-f (x , p))))
            (!ᵈ (from-lemma (f x p)) ∙ᵈ snd= (f-tot.g-f (x , p)))

replace-inverse : ∀ {i j} {A : Type i} {B : Type j} {f : A → B}
  (f-ise : is-equiv f) {g₁ : B → A}
  → is-equiv.g f-ise ∼ g₁ → is-equiv f
replace-inverse {f = f} f-ise {g₁ = g₁} g∼ =
  is-eq f g₁ (λ b → ap f (! (g∼ b)) ∙ f-g b) (λ a → ! (g∼ (f a)) ∙ g-f a)
  where open is-equiv f-ise

-- some lemmas for rearranging identity types

module _ {i} {A : Type i} where

  pre-rotate-in-≃ : {a a' a'' : A} (q : a' == a'') (p : a == a') {r : a == a''}
    → (r == p ∙ q) ≃ (! p ∙' r == q)
  pre-rotate-in-≃ q idp {r = idp} = equiv (λ c → c) (λ c → c) (λ _ → idp) λ _ → idp

  pre-rotate-in-≃-back : {a a' a'' : A} (q : a' == a'') (p : a == a') {r : a == a''}
    → (! p ∙' r == q) ≃ (r == p ∙ q)
  pre-rotate-in-≃-back q p = (pre-rotate-in-≃ q p)⁻¹

  pre-rotate-in-!≃ : {a a' a'' : A} (q : a' == a'') (p : a' == a) {r : a == a''}
    → (r == ! p ∙ q) ≃ (p ∙' r == q)
  pre-rotate-in-!≃ q idp {r = idp} = equiv (λ c → c) (λ c → c) (λ _ → idp) λ _ → idp

  pre-rotate-in-!≃-back : {a a' a'' : A} (q : a' == a'') (p : a' == a) {r : a == a''}
    → (p ∙' r == q) ≃ (r == ! p ∙ q)
  pre-rotate-in-!≃-back q p = (pre-rotate-in-!≃ q p)⁻¹
