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

is-contr-map : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
  → Type (lmax i j)
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

  lcoh : (f : A → B) → linv f → Type (lmax i j)
  lcoh f (g , g-f) = Σ (∀ y → f (g y) == y)
                       (λ f-g → ∀ y → ap g (f-g y) == g-f (g y))

  rcoh : (f : A → B) → rinv f → Type (lmax i j)
  rcoh f (g , f-g) = Σ (∀ x → g (f x) == x)
                       (λ g-f → ∀ x → ap f (g-f x) == f-g (f x))


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

{-
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
-}

∘e-unit-r : ∀ {i} {A B : Type i} (e : A ≃ B) → (e ∘e ide A) == e
∘e-unit-r e = pair= idp (prop-has-all-paths _ _)

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

{-
module _ {i} (A : Type i) where

  ap-ua-idf-idp : 
    ap ua (ap (idf A ,_)
      (prop-has-all-paths (snd (ide A)) (snd (ide A))))
      ==
    idp
  ap-ua-idf-idp =
    ap (ap ua) (ap (ap (idf A ,_)) (prop-has-all-paths {{has-level-apply-instance}} _ _))    
  
  ua-∘e-al-aux4 : (ω : ua (ide A) == ua (ide A) ∙ ua (ide A)) →
    ∙-assoc (ua (ide A)) (ua (ide A)) (ua (ide A)) ∙
    ap (_∙_ (ua (ide A))) (! ω) ∙
    ! ω ∙ ω ∙
    ! (ap (λ v → v ∙ ua (ide A)) (! ω))
      ==
    idp
  ua-∘e-al-aux4 =
    transport
      (λ p → ∀ (ω : p == p ∙ p) →
        ∙-assoc p p p ∙ ap (_∙_ p) (! ω) ∙ ! ω ∙ ω ∙
        ! (ap (λ v → v ∙ p) (! ω))
          ==
        idp) (! (ua-η idp)) (λ ω → =ₛ-out (aux ω))
    where
      aux : (ω : idp == idp)
        →
        ap (λ x → x) (! ω) ◃∙ ! ω ◃∙ ω ◃∙ ! (ap (λ v → v ∙ idp) (! ω)) ◃∎
          =ₛ
        idp ◃∎
      aux ω = 
        ap (λ x → x) (! ω) ◃∙ ! ω ◃∙ ω ◃∙ ! (ap (λ v → v ∙ idp) (! ω)) ◃∎
          =ₛ₁⟨ 1 & 2 & !-inv-l ω ⟩
        ap (λ x → x) (! ω) ◃∙ idp ◃∙ ! (ap (λ v → v ∙ idp) (! ω)) ◃∎
          =ₛ₁⟨ 0 & 1 & ap-idf (! ω) ⟩
        ! ω ◃∙ idp ◃∙ ! (ap (λ v → v ∙ idp) (! ω)) ◃∎
          =ₛ₁⟨ 2 & 1 & ap ! (ap-! (λ v → v ∙ idp) ω) ∙ !-! (ap (λ v → v ∙ idp) ω) ⟩
        ! ω ◃∙ idp ◃∙ ap (λ v → v ∙ idp) ω ◃∎
          =ₛ₁⟨ !-unit-r-inv ω ⟩
        idp ◃∎ ∎ₛ

  ua-∘e-al-aux3 : {e₁ e₂ : A ≃ A} (ω : e₁ == e₂) →
    ! (ap (λ z → ua (z ∘e ide A)) ω) ◃∙
    ap ua (pair= idp (prop-has-all-paths _ _)) ◃∙
    ap ua (ap (_∘e_ (ide A)) ω) ◃∎
      =ₛ
    ap ua (pair= idp (prop-has-all-paths _ _)) ◃∎
  ua-∘e-al-aux3 {e₁} idp =
    =ₛ-in (∙-unit-r _ ∙ ap (ap ua) (ap (ap (–> e₁ ,_))
      (prop-has-all-paths {{has-level-apply-instance}} _ _)))
      
  ua-∘e-al-aux2 : (ω₁ : ua (ide A) == ua (ide A) ∙ ua (ide A))
    {e : A ≃ A} (ω₂ : e == ide A) →
    ∙-assoc (ua (ide A)) (ua (ide A)) (ua (ide A)) ◃∙
    ap (λ v → ua (ide A) ∙ v)
      (! (ap ua ω₂ ∙ ω₁)) ◃∙
    ap (λ z → ua (ide A) ∙ ua z) ω₂ ◃∙
    ! (ap ua ω₂ ∙ ω₁) ◃∙
    ap ua (pair= idp (prop-has-all-paths _ _)) ◃∙
    (ap ua ω₂ ∙ ω₁) ◃∙
    ! (ap (λ q → q ∙ ua (ide A)) (ap ua ω₂)) ◃∙
    ! (ap (λ v → v ∙ ua (ide A)) (! (ap ua ω₂ ∙ ω₁))) ◃∎
      =ₛ
    idp ◃∎
  ua-∘e-al-aux2 ω₁ idp = 
    ∙-assoc (ua (ide A)) (ua (ide A)) (ua (ide A)) ◃∙
    ap (_∙_ (ua (ide A))) (! ω₁) ◃∙
    idp ◃∙
    ! ω₁ ◃∙
    ap ua (ap (fst (ide A) ,_)
      (prop-has-all-paths (snd (ide A)) (snd (ide A)))) ◃∙
    ω₁ ◃∙
    idp ◃∙
    ! (ap (λ v → v ∙ ua (ide A)) (! ω₁)) ◃∎
      =ₛ₁⟨ 4 & 1 & ap-ua-idf-idp ⟩
    ∙-assoc (ua (ide A)) (ua (ide A)) (ua (ide A)) ◃∙
    ap (_∙_ (ua (ide A))) (! ω₁) ◃∙
    idp ◃∙
    ! ω₁ ◃∙
    idp ◃∙
    ω₁ ◃∙
    idp ◃∙
    ! (ap (λ v → v ∙ ua (ide A)) (! ω₁)) ◃∎
      =ₛ₁⟨ ua-∘e-al-aux4 ω₁ ⟩
    idp ◃∎ ∎ₛ
    
  ua-∘e-al-aux :
    ∙-assoc (ua (ide A)) (ua (ide A)) (ua (ide A)) ◃∙
    ap (λ v → ua (ide A) ∙ v) (! (ua-∘e (ide A) (ide A))) ◃∙
    ! (ua-∘e (ide A) (ide A ∘e ide A)) ◃∙
    ap ua (pair= idp (prop-has-all-paths _ _)) ◃∙
    ua-∘e (ide A ∘e ide A) (ide A) ◃∙
    ! (ap (λ v → v ∙ ua (ide A)) (! (ua-∘e (ide A) (ide A)))) ◃∎
      =ₛ
    idp ◃∎
  ua-∘e-al-aux =
    ∙-assoc (ua (ide A)) (ua (ide A)) (ua (ide A)) ◃∙
    ap (λ v → ua (ide A) ∙ v) (! (ua-∘e (ide A) (ide A))) ◃∙
    ! (ua-∘e (ide A) (ide A ∘e ide A)) ◃∙
    ap ua (pair= idp (prop-has-all-paths _ _)) ◃∙
    ua-∘e (ide A ∘e ide A) (ide A) ◃∙
    ! (ap (λ v → v ∙ ua (ide A)) (! (ua-∘e (ide A) (ide A)))) ◃∎
      =ₛ₁⟨ 1 & 1 & ap (ap (λ v → ua (ide A) ∙ v)) (ap ! (ua-∘e-β (ide A))) ⟩
    _
      =ₛ₁⟨ 2 & 1 & ap ! (ua-∘e-β (ide A ∘e ide A)) ⟩
    _
      =ₛ₁⟨ 5 & 1 & ap ! (ap (ap (λ v → v ∙ ua (ide A))) (ap ! (ua-∘e-β (ide A)))) ⟩
    ∙-assoc (ua (ide A)) (ua (ide A)) (ua (ide A)) ◃∙
    ap (λ v → ua (ide A) ∙ v)
      (! (ap ua (∘e-unit-r (ide A)) ∙
        ap (λ w → w ∙ ua (ide A)) (! (ua-η idp)))) ◃∙
    ! (ap ua (∘e-unit-r (ide A ∘e ide A)) ∙
      ap (λ w → w ∙ ua (ide A ∘e ide A)) (! (ua-η idp))) ◃∙
    ap ua (pair= idp (prop-has-all-paths _ _)) ◃∙
    ua-∘e (ide A ∘e ide A) (ide A) ◃∙
    ! (ap (λ v → v ∙ ua (ide A)) (! (ap ua (∘e-unit-r (ide A)) ∙
      ap (λ w → w ∙ ua (ide A)) (! (ua-η idp))))) ◃∎
      =ₛ⟨ 4 & 1 & ua-∘e-coh (ide A) (∘e-unit-r (ide A)) ⟩
    ∙-assoc (ua (ide A)) (ua (ide A)) (ua (ide A)) ◃∙
    ap (λ v → ua (ide A) ∙ v)
      (! (ap ua (∘e-unit-r (ide A)) ∙
        ap (λ w → w ∙ ua (ide A)) (! (ua-η idp)))) ◃∙
    ! (ap ua (∘e-unit-r (ide A ∘e ide A)) ∙
      ap (λ w → w ∙ ua (ide A ∘e ide A)) (! (ua-η idp))) ◃∙
    ap ua (pair= idp (prop-has-all-paths _ _)) ◃∙
    ap ua (ap (_∘e_ (ide A)) (∘e-unit-r (ide A))) ◃∙
    ua-∘e (ide A) (ide A) ◃∙
    ! (ap (λ q → q ∙ ua (ide A)) (ap ua (∘e-unit-r (ide A)))) ◃∙
    ! (ap (λ v → v ∙ ua (ide A)) (! (ap ua (∘e-unit-r (ide A)) ∙
      ap (λ w → w ∙ ua (ide A)) (! (ua-η idp))))) ◃∎
      =ₛ₁⟨ 5 & 1 & ua-∘e-β (ide A) ⟩
    ∙-assoc (ua (ide A)) (ua (ide A)) (ua (ide A)) ◃∙
    ap (λ v → ua (ide A) ∙ v)
      (! (ap ua (∘e-unit-r (ide A)) ∙
        ap (λ w → w ∙ ua (ide A)) (! (ua-η idp)))) ◃∙
    ! (ap ua (∘e-unit-r (ide A ∘e ide A)) ∙
      ap (λ w → w ∙ ua (ide A ∘e ide A)) (! (ua-η idp))) ◃∙
    ap ua (pair= idp (prop-has-all-paths _ _)) ◃∙
    ap ua (ap (_∘e_ (ide A)) (∘e-unit-r (ide A))) ◃∙
    (ap ua (∘e-unit-r (ide A)) ∙
      ap (λ w → w ∙ ua (ide A)) (! (ua-η idp))) ◃∙
    ! (ap (λ q → q ∙ ua (ide A)) (ap ua (∘e-unit-r (ide A)))) ◃∙
    ! (ap (λ v → v ∙ ua (ide A)) (! (ap ua (∘e-unit-r (ide A)) ∙
      ap (λ w → w ∙ ua (ide A)) (! (ua-η idp))))) ◃∎
      =ₛ⟨ 2 & 1 &
        hmtpy-nat-!◃ (λ z → ap ua (∘e-unit-r z) ∙ ap (λ w → w ∙ ua z) (! (ua-η idp))) (∘e-unit-r (ide A)) ⟩
    ∙-assoc (ua (ide A)) (ua (ide A)) (ua (ide A)) ◃∙
    ap (λ v → ua (ide A) ∙ v)
      (! (ap ua (∘e-unit-r (ide A)) ∙
        ap (λ w → w ∙ ua (ide A)) (! (ua-η idp)))) ◃∙
    ap (λ z → ua (ide A) ∙ ua z) (∘e-unit-r (ide A)) ◃∙
    ! (ap ua (∘e-unit-r (ide A)) ∙ ap (λ w → w ∙ ua (ide A)) (! (ua-η idp))) ◃∙
    ! (ap (λ z → ua (z ∘e ide A)) (∘e-unit-r (ide A))) ◃∙
    ap ua (pair= idp (prop-has-all-paths _ _)) ◃∙
    ap ua (ap (_∘e_ (ide A)) (∘e-unit-r (ide A))) ◃∙
    (ap ua (∘e-unit-r (ide A)) ∙
      ap (λ w → w ∙ ua (ide A)) (! (ua-η idp))) ◃∙
    ! (ap (λ q → q ∙ ua (ide A)) (ap ua (∘e-unit-r (ide A)))) ◃∙
    ! (ap (λ v → v ∙ ua (ide A)) (! (ap ua (∘e-unit-r (ide A)) ∙
      ap (λ w → w ∙ ua (ide A)) (! (ua-η idp))))) ◃∎
      =ₛ⟨ 4 & 3 & ua-∘e-al-aux3 (∘e-unit-r (ide A)) ⟩
    _
      =ₛ⟨ ua-∘e-al-aux2 (ap (λ w → w ∙ ua (ide A)) (! (ua-η idp))) (∘e-unit-r (ide A)) ⟩
    idp ◃∎ ∎ₛ

ua-∘e-al : ∀ {i} {A B C D : Type i} (e₁ : A ≃ B) (e₂ : B ≃ C) (e₃ : C ≃ D)
  →
  ∙-assoc (ua e₁) (ua e₂) (ua e₃) ◃∙
  ap (λ v → ua e₁ ∙ v) (! (ua-∘e e₂ e₃)) ◃∙
  ! (ua-∘e e₁ (e₃ ∘e e₂)) ◃∎
    =ₛ
  ap (λ v → v ∙ ua e₃) (! (ua-∘e e₁ e₂)) ◃∙
  ! (ua-∘e (e₂ ∘e e₁) e₃) ◃∙
  ! (ap ua (pair= idp (prop-has-all-paths _ _))) ◃∎
ua-∘e-al {i} =
  equiv-induction-tri
    (λ {A B C D} e₁ e₂ e₃ → 
      ∙-assoc (ua e₁) (ua e₂) (ua e₃) ◃∙
      ap (λ v → ua e₁ ∙ v) (! (ua-∘e e₂ e₃)) ◃∙
      ! (ua-∘e e₁ (e₃ ∘e e₂)) ◃∎
        =ₛ
      ap (λ v → v ∙ ua e₃) (! (ua-∘e e₁ e₂)) ◃∙
      ! (ua-∘e (e₂ ∘e e₁) e₃) ◃∙
      ! (ap ua (pair= idp (prop-has-all-paths _ _))) ◃∎)
    (λ A →
      ∙-assoc (ua (ide A)) (ua (ide A)) (ua (ide A)) ◃∙
      ap (λ v → ua (ide A) ∙ v) (! (ua-∘e (ide A) (ide A))) ◃∙
      ! (ua-∘e (ide A) (ide A ∘e ide A)) ◃∎
        =ₛ⟨ post-rotate-in (post-rotate-in (post-rotate'-out (ua-∘e-al-aux A))) ⟩
      idp ◃∙
      ap (λ v → v ∙ ua (ide A)) (! (ua-∘e (ide A) (ide A))) ◃∙
      ! (ua-∘e (ide A ∘e ide A) (ide A)) ◃∙
      ! (ap ua (pair= idp (prop-has-all-paths _ _))) ◃∎
        =ₛ₁⟨ 0 & 2 & idp ⟩
      ap (λ v → v ∙ ua (ide A)) (! (ua-∘e (ide A) (ide A))) ◃∙
      ! (ua-∘e (ide A ∘e ide A) (ide A)) ◃∙
      ! (ap ua (pair= idp (prop-has-all-paths _ _))) ◃∎ ∎ₛ )      
-}
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
