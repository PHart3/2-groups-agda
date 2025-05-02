{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.Equivalence2
open import lib.NType2
open import lib.FTID
open import lib.types.Bool
open import lib.types.Empty
open import lib.types.Paths
open import lib.types.Pi
open import lib.types.Sigma

{-
This file contains various lemmas that rely on lib.types.Paths or
functional extensionality for pointed maps.
-}

module lib.types.Pointed where

{- Pointed maps -}

⊙app= : ∀ {i j} {X : Ptd i} {Y : Ptd j} {f g : X ⊙→ Y}
  → f == g → f ⊙∼ g
⊙app= {X = X} {Y = Y} p =
  app= (fst= p) , ↓-ap-in (_== pt Y) (λ u → u (pt X)) (snd= p)

-- function extensionality for pointed maps
⊙λ= : ∀ {i j} {X : Ptd i} {Y : Ptd j} {f g : X ⊙→ Y}
  → f ⊙∼ g → f == g
⊙λ= {g = g} (p , α) = pair= (λ= p)
  (↓-app=cst-in (↓-idf=cst-out α ∙ ap (_∙ snd g) (! (app=-β p _))))

⊙λ=' : ∀ {i j} {X : Ptd i} {Y : Ptd j} {f g : X ⊙→ Y}
  (p : fst f ∼ fst g)
  (α : snd f == snd g [ (λ y → y == pt Y) ↓ p (pt X) ])
  → f == g
⊙λ=' {g = g} = curry ⊙λ=

-- associativity of pointed maps
⊙∘-assoc-pt : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
  {a₁ a₂ : A} (f : A → B) {b : B} (g : B → C) {c : C}
  (p : a₁ == a₂) (q : f a₂ == b) (r : g b == c)
  → ⊙∘-pt (g ∘ f) p (⊙∘-pt g q r) == ⊙∘-pt g (⊙∘-pt f p q) r
⊙∘-assoc-pt _ _ idp _ _ = idp

⊙∘-assoc : ∀ {i j k l} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {W : Ptd l}
  (h : Z ⊙→ W) (g : Y ⊙→ Z) (f : X ⊙→ Y)
  → ((h ⊙∘ g) ⊙∘ f) ⊙∼ (h ⊙∘ (g ⊙∘ f))
⊙∘-assoc (h , hpt) (g , gpt) (f , fpt) = (λ _ → idp) , ⊙∘-assoc-pt g h fpt gpt hpt

⊙∘-cst-l : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  → (f : X ⊙→ Y) → (⊙cst :> (Y ⊙→ Z)) ⊙∘ f ⊙∼ ⊙cst
⊙∘-cst-l {Z = Z} f = (λ _ → idp) , ap (_∙ idp) (ap-cst (pt Z) (snd f))

⊙∘-cst-r : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  → (f : Y ⊙→ Z) → f ⊙∘ (⊙cst :> (X ⊙→ Y)) ⊙∼ ⊙cst
⊙∘-cst-r {X = X} f = (λ _ → snd f) , ↓-idf=cst-in' idp

module _ {i j} {X : Ptd i} {Y : Ptd j} (f : X ⊙→ Y) where

  ⊙∘-lunit : f ⊙-comp ⊙idf Y ⊙∘ f
  fst ⊙∘-lunit x = idp
  snd ⊙∘-lunit = ! (∙-unit-r (ap (λ x → x) (snd f)) ∙ ap-idf (snd f))

  ⊙∘-runit : f ⊙-comp f ⊙∘ ⊙idf X
  fst ⊙∘-runit x = idp
  snd ⊙∘-runit = idp

-- inverse of homotopy of pointed maps

module _ {i j} {X : Ptd i} {Y : Ptd j} where

  !-⊙∼ : {f₁ f₂ : X ⊙→ Y} (H : f₁ ⊙-comp f₂) → f₂ ⊙-comp f₁
  fst (!-⊙∼ (H₀ , H₁)) x = ! (H₀ x)
  snd (!-⊙∼ {f₁} {f₂} (H₀ , H₁)) =
    ap (λ p → p ∙ snd f₂) (!-! (H₀ (pt (X)))) ∙
    ap (λ p → H₀ (pt X) ∙ p) (! H₁) ∙
    ! (∙-assoc (H₀ (pt X)) (! (H₀ (pt X))) (snd f₁)) ∙
    ap (λ p → p ∙ snd f₁) (!-inv-r (H₀ (pt X)))

-- identity homotopy of pointed maps

  ⊙∼-id : (f : X ⊙→ Y) → f ⊙-comp f
  fst (⊙∼-id (f , fₚ)) x = idp
  snd (⊙∼-id (f , fₚ)) = idp

module _ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} where 

  ⊙∘-assoc-comp : ∀ {l} {W : Ptd l} (h : Z ⊙→ W) (g : Y ⊙→ Z) (f : X ⊙→ Y)
    → ((h ⊙∘ g) ⊙∘ f) ⊙-comp (h ⊙∘ (g ⊙∘ f))
  fst (⊙∘-assoc-comp (h , hpt) (g , gpt) (f , fpt)) = λ x → idp
  snd (⊙∘-assoc-comp (h , hpt) (g , gpt) (f , fpt)) =
    ! (∙-assoc (ap (h ∘ g) fpt) (ap h gpt) hpt) ∙
    ap (λ p → p ∙ hpt) (ap (λ p → p ∙ ap h gpt) (ap-∘ h g fpt)) ∙
    ap (λ p → p ∙ hpt) (∙-ap h (ap g fpt) gpt)

  ⊙∘-α-comp : ∀ {l} {W : Ptd l} (h : Z ⊙→ W) (g : Y ⊙→ Z) (f : X ⊙→ Y)
    → h ⊙∘ g ⊙∘ f ⊙-comp (h ⊙∘ g) ⊙∘ f
  ⊙∘-α-comp h g f = !-⊙∼ (⊙∘-assoc-comp h g f)

-- pre- and post-comp on (unfolded) homotopies of pointed maps

  ⊙∘-post : {f₁ f₂ : X ⊙→ Y} (g : Y ⊙→ Z) (H : f₁ ⊙-comp f₂) → g ⊙∘ f₁ ⊙-comp g ⊙∘ f₂
  fst (⊙∘-post g H) = λ x → ap (fst g) (fst H x)
  snd (⊙∘-post {f₁} g H) =
    ! (∙-assoc (! (ap (fst g) (fst H (pt X)))) (ap (fst g) (snd f₁)) (snd g)) ∙
    ap (λ p → p ∙ snd g) (!-ap-∙ (fst g) (fst H (pt X)) (snd f₁)) ∙
    ap (λ p → p ∙ snd g) (ap (ap (fst g)) (snd H))

  ⊙∘-pre : {f₁ f₂ : X ⊙→ Y} (g : Z ⊙→ X) (H : f₁ ⊙-comp f₂) → f₁ ⊙∘ g ⊙-comp f₂ ⊙∘ g
  fst (⊙∘-pre g H) = λ x → fst H (fst g x)
  snd (⊙∘-pre {f₁} {f₂} g H) =
    ! (∙-assoc (! (fst H (fst g (pt Z)))) (ap (fst f₁) (snd g)) (snd f₁)) ∙
    ap (λ p → p ∙ snd f₁) (hmtpy-nat-!-sq (fst H) (snd g)) ∙
    ∙-assoc (ap (fst f₂) (snd g)) (! (fst H (pt X))) (snd f₁) ∙
    ap (λ p → ap (fst f₂) (snd g) ∙ p) (snd H)
    
-- concatenation of homotopies of pointed maps

module _ {i j} {X : Ptd i} {Y : Ptd j} {f₁ f₂ f₃ : X ⊙→ Y} where 

  infixr 15 _∙⊙∼_
  _∙⊙∼_ : f₁ ⊙-comp f₂ → f₂ ⊙-comp f₃ → f₁ ⊙-comp f₃
  fst (H₁ ∙⊙∼ H₂) = λ x → fst H₁ x ∙ fst H₂ x 
  snd (H₁ ∙⊙∼ H₂) =
    ap (λ p → ! (p ∙ fst H₂ (pt X)) ∙ snd f₁) (tri-exch (snd H₁)) ∙ 
    ap (λ p → ! ((snd f₁ ∙ ! (snd f₂)) ∙ p) ∙ snd f₁) (tri-exch (snd H₂)) ∙
    !3-∙3 (snd f₁) (snd f₂) (snd f₃)

-- homotopies of homotopies of pointed maps

module _ {i j} {X : Ptd i} {Y : Ptd j} where

  infixr 10 _⊙→∼_
  _⊙→∼_ : {f g : X ⊙→ Y} (H₁ H₂ : f ⊙-comp g) → Type (lmax i j)
  _⊙→∼_ {f = f} H₁ H₂ =
    Σ (fst H₁ ∼ fst H₂)
      (λ K → ap (λ p →  ! p ∙ snd f) (K (pt X)) ∙ snd H₂ == snd H₁)

  ⊙→∼-id : {f g : X ⊙→ Y} (H : f ⊙-comp g) → H ⊙→∼ H
  fst (⊙→∼-id H) = λ x → idp
  snd (⊙→∼-id H) = idp

-- pointed sections

  record has-sect⊙ (f : X ⊙→ Y) : Type (lmax i j) where
    constructor sect⊙
    field
      r-inv : Y ⊙→ X
      sect⊙-eq : f ⊙∘ r-inv == ⊙idf Y

-- induction principle for ⊙-comp

module _ {i j} {X : Ptd i} {Y : Ptd j} (f : X ⊙→ Y) where

  ⊙hom-contr-aux :
    is-contr
      (Σ (Σ (de⊙ X → de⊙ Y) (λ g → fst f ∼ g))
        (λ (h , K) → Σ (h (pt X) == pt Y) (λ p → (! (K (pt X)) ∙ snd f == p))))
  ⊙hom-contr-aux =
    equiv-preserves-level
      ((Σ-contr-red
        {P = λ (h , K) → Σ (h (pt X) == pt Y) (λ p → (! (K (pt X)) ∙ snd f == p))}
        (funhom-contr {f = fst f}))⁻¹)

  abstract
    ⊙hom-contr : is-contr (Σ (X ⊙→ Y) (λ g → f ⊙-comp g))
    ⊙hom-contr = equiv-preserves-level lemma {{⊙hom-contr-aux}}
      where
        lemma :
          Σ (Σ (de⊙ X → de⊙ Y) (λ g → fst f ∼ g))
            (λ (h , K) → Σ (h (pt X) == pt Y) (λ p → (! (K (pt X)) ∙ snd f == p)))
            ≃
          Σ (X ⊙→ Y) (λ g → f ⊙-comp g)
        lemma =
          equiv
            (λ ((g , K) , (p , H)) → (g , p) , (K , H))
            (λ ((h , p) , (H , K)) → (h , H) , (p , K))
            (λ ((h , p) , (H , K)) → idp)
            λ ((g , K) , (p , H)) → idp

  ⊙hom-ind : ∀ {k} (P : (g : X ⊙→ Y) → (f ⊙-comp g → Type k))
    → P f (⊙∼-id f) → {g : X ⊙→ Y} (p : f ⊙-comp g) → P g p
  ⊙hom-ind P = ID-ind-map P ⊙hom-contr

  ⊙hom-ind-β : ∀ {k} (P : (g : X ⊙→ Y) → (f ⊙-comp g → Type k))
    → (r : P f (⊙∼-id f)) → ⊙hom-ind P r {f} (⊙∼-id f) == r
  ⊙hom-ind-β P = ID-ind-map-β P ⊙hom-contr

module _ {i j} {X : Ptd i} {Y : Ptd j} where

  ⊙-comp-to-== : {f : X ⊙→ Y} {g : X ⊙→ Y} → f ⊙-comp g → f == g
  ⊙-comp-to-== {f} = ⊙hom-ind f (λ g _ → f == g) idp

  ⊙-comp-to-==-β : (f : X ⊙→ Y) → ⊙-comp-to-== (⊙∼-id f) == idp
  ⊙-comp-to-==-β f = ⊙hom-ind-β f (λ g _ → f == g) idp

  ==-to-⊙-comp : {f : X ⊙→ Y} {g : X ⊙→ Y} → f == g → f ⊙-comp g
  ==-to-⊙-comp idp = ⊙∼-id _

  ⊙-comp-==-≃ : {f : X ⊙→ Y} {g : X ⊙→ Y} → (f == g) ≃ (f ⊙-comp g)
  ⊙-comp-==-≃ {f} {g} = equiv ==-to-⊙-comp ⊙-comp-to-== aux1 aux2
    where
      aux1 : {k : X ⊙→ Y} (H : f ⊙-comp k) → ==-to-⊙-comp (⊙-comp-to-== H) == H
      aux1 =
        ⊙hom-ind f (λ k H → ==-to-⊙-comp (⊙-comp-to-== H) == H)
          (ap (==-to-⊙-comp) (⊙-comp-to-==-β f))

      aux2 : {k : X ⊙→ Y} (p : f == k) → ⊙-comp-to-== (==-to-⊙-comp p) == p
      aux2 idp = ⊙-comp-to-==-β f 

-- induction principle for ⊙∼→

module _ {i j} {X : Ptd i} {Y : Ptd j} {f₁ f₂ : X ⊙→ Y} {H : f₁ ⊙-comp f₂} where

  ⊙→∼-contr-aux :
    is-contr $
      Σ (Σ (fst f₁ ∼ fst f₂) (λ h → fst H ∼ h))
        (λ (h , k) → Σ (! (h (pt X)) ∙ snd f₁ == snd f₂)
          (λ L → ap (λ p →  ! p ∙ snd f₁) (k (pt X)) ∙ L == snd H))
  ⊙→∼-contr-aux =
    equiv-preserves-level
      ((Σ-contr-red
        {P = λ (h , k) →
          Σ (! (h (pt X)) ∙ snd f₁ == snd f₂) (λ L → ap (λ p →  ! p ∙ snd f₁) (k (pt X)) ∙ L == snd H)}
        (funhom-contr {f = fst H}))⁻¹)

  abstract
    ⊙→∼-contr : is-contr (Σ (f₁ ⊙-comp f₂) (λ K → H ⊙→∼ K))
    ⊙→∼-contr = equiv-preserves-level lemma {{⊙→∼-contr-aux}}
      where
        lemma :
          Σ (Σ (fst f₁ ∼ fst f₂) (λ h → fst H ∼ h))
            (λ (h , k) → Σ (! (h (pt X)) ∙ snd f₁ == snd f₂)
              (λ L → ap (λ p →  ! p ∙ snd f₁) (k (pt X)) ∙ L == snd H))
            ≃
          Σ (f₁ ⊙-comp f₂) (λ K → H ⊙→∼ K)
        lemma =
          equiv
            (λ ((h , k) , (L , c)) → (h , L) , (k , c))
            (λ ((K₁ , K₂) , (c₁ , c₂)) → (K₁ , c₁) , (K₂ , c₂))
            (λ ((K₁ , K₂) , (c₁ , c₂)) → idp)
            λ ((h , k) , (L , c)) → idp

  ⊙→∼-ind : ∀ {k} (P : (K : f₁ ⊙-comp f₂) → (H ⊙→∼ K → Type k))
    → P H (⊙→∼-id H) → {K : f₁ ⊙-comp f₂} (p : H ⊙→∼ K) → P K p
  ⊙→∼-ind P = ID-ind-map P ⊙→∼-contr

module _ {i j} {X : Ptd i} {Y : Ptd j} {f g : X ⊙→ Y} {H₁ H₂ : f ⊙-comp g} where

  ⊙→∼-to-== : H₁ ⊙→∼ H₂ → H₁ == H₂
  ⊙→∼-to-== = ⊙→∼-ind {H = H₁} (λ H₂ _ → H₁ == H₂) idp 

module _ {i j} {X : Ptd i} {Y : Ptd j} where

 ∙⊙∼-! : (f : X ⊙→ Y) → !-⊙∼ (⊙∼-id f) == ⊙∼-id f
 ∙⊙∼-! (f₀ , idp) = ⊙→∼-to-== ((λ _ → idp) , idp)

 ∙⊙∼-unit-l : {f g : X ⊙→ Y} (H : f ⊙-comp g) → (⊙∼-id f ∙⊙∼ H) == H
 ∙⊙∼-unit-l {f = (f₀ , idp)} H = ⊙→∼-to-== ((λ _ → idp) , aux (snd H))
   where
     aux : ∀ {k} {A : Type k} {x y : A} {r : y == x} {q₂ : x == y} (q₁ : ! r ∙ idp == q₂) →
       q₁ == ap (λ p → ! p ∙ idp) (tri-exch q₁) ∙ ∙-unit-r (! (! q₂)) ∙ !-! q₂
     aux {r = idp} idp = idp

 ∙⊙∼-unit-r : {f g : X ⊙→ Y} (H : f ⊙-comp g)→ (H ∙⊙∼ ⊙∼-id g) == H
 ∙⊙∼-unit-r {g = (g₀ , idp)} H = ⊙→∼-to-== ((λ x → ∙-unit-r (fst H x)) , aux {r = fst H (pt X)} (snd H))
   where
     aux : ∀ {k} {A : Type k} {x y : A} {r q₂ : x == y} (q₁ : ! r ∙ q₂ == idp) →
       ap (λ p → ! p ∙ q₂) (∙-unit-r r) ∙ q₁
         ==
       ap (λ p → ! (p ∙ idp) ∙ q₂) (tri-exch q₁) ∙ !3-∙3 q₂ idp idp
     aux {r = idp} idp = idp

module _ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} where

  ∙⊙-post : {f : X ⊙→ Y} {g : Y ⊙→ Z} → ⊙∘-post g (⊙∼-id f) == ⊙∼-id (g ⊙∘ f)
  ∙⊙-post = ⊙→∼-to-== ((λ _ → idp) , idp)

  ∙⊙-pre : {f : X ⊙→ Y} {g : Z ⊙→ X} → ⊙∘-pre g (⊙∼-id f) == ⊙∼-id (f ⊙∘ g)
  ∙⊙-pre {g = (g₀ , idp)} = ⊙→∼-to-== ((λ _ → idp) , idp)

{- Pointed equivalences -}

-- Extracting data from an pointed equivalence
module _ {i j} {X : Ptd i} {Y : Ptd j} (⊙e : X ⊙≃ Y) where

  ⊙≃-to-≃ : de⊙ X ≃ de⊙ Y
  ⊙≃-to-≃ = fst (fst ⊙e) , snd ⊙e

  ⊙–> : X ⊙→ Y
  ⊙–> = fst ⊙e

  ⊙–>-pt = snd ⊙–>

  ⊙<– : Y ⊙→ X
  ⊙<– = is-equiv.g (snd ⊙e) , lemma ⊙e where
    lemma : {Y : Ptd j} (⊙e : X ⊙≃ Y) → is-equiv.g (snd ⊙e) (pt Y) == pt X
    lemma ((f , idp) , f-ise) = is-equiv.g-f f-ise (pt X)

  ⊙<–-pt = snd ⊙<–

  infix 120 _⊙⁻¹
  _⊙⁻¹ : Y ⊙≃ X
  _⊙⁻¹ = ⊙<– , is-equiv-inverse (snd ⊙e)

module _ {i j} {X : Ptd i} {Y : Ptd j} where 

  ⊙<–-inv-l : (⊙e : X ⊙≃ Y) → ⊙<– ⊙e ⊙∘ ⊙–> ⊙e ⊙∼ ⊙idf _
  ⊙<–-inv-l ⊙e = <–-inv-l (⊙≃-to-≃ ⊙e) , ↓-idf=cst-in' (lemma ⊙e) where
    lemma : {Y : Ptd j} (⊙e : X ⊙≃ Y)
      → snd (⊙<– ⊙e ⊙∘ ⊙–> ⊙e) == is-equiv.g-f (snd ⊙e) (pt X)
    lemma ((f , idp) , f-ise) = idp

  ⊙<–-inv-l-comp : (⊙e : X ⊙≃ Y) → ⊙<– ⊙e ⊙∘ ⊙–> ⊙e ⊙-comp ⊙idf _
  ⊙<–-inv-l-comp ⊙e = ⊙-to-comp (⊙<–-inv-l ⊙e)

  ⊙<–-inv-r : (⊙e : X ⊙≃ Y) → ⊙–> ⊙e ⊙∘ ⊙<– ⊙e ⊙∼ ⊙idf _
  ⊙<–-inv-r ⊙e = <–-inv-r (⊙≃-to-≃ ⊙e) , ↓-idf=cst-in' (lemma ⊙e) where
    lemma : {Y : Ptd j} (⊙e : X ⊙≃ Y)
      → snd (⊙–> ⊙e ⊙∘ ⊙<– ⊙e) == is-equiv.f-g (snd ⊙e) (pt Y)
    lemma ((f , idp) , f-ise) = ∙-unit-r _ ∙ is-equiv.adj f-ise (pt X)

module _ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} (⊙e : X ⊙≃ Y) where

  post⊙∘-is-equiv : is-equiv (λ (k : Z ⊙→ X) → ⊙–> ⊙e ⊙∘ k)
  post⊙∘-is-equiv = is-eq (⊙–> ⊙e ⊙∘_) (⊙<– ⊙e ⊙∘_) (to-from ⊙e) (from-to ⊙e) where
    abstract
      to-from : {Y = Y₁ : Ptd j} (⊙e₁ : _⊙≃_ {i} {j} X Y₁)
                (k₁ : _⊙→_ {k} {j} Z Y₁) →
                _==_ {lmax j k}
                {Σ {lmax j k} {j} (de⊙ Z → de⊙ Y₁)
                (λ f → _==_ {j} {de⊙ Y₁} (f (pt Z)) (pt Y₁))}
                (_⊙∘_ {k} {i} {j} {Z} {X} {Y₁} (⊙–> {i} {j} {X} {Y₁} ⊙e₁)
                (_⊙∘_ {k} {j} {i} {Z} {Y₁} {X} (⊙<– {i} {j} {X} {Y₁} ⊙e₁) k₁))
                k₁
      to-from ((f , idp) , f-ise) (k , k-pt) = ⊙λ=' (f.f-g ∘ k) (↓-idf=cst-in' $ lemma k-pt)
        where
          module f = is-equiv {i} {j} f-ise
          lemma : ∀ {y₀} (k-pt : y₀ == f (pt X))
            → ⊙∘-pt f (⊙∘-pt f.g k-pt (f.g-f _)) idp == f.f-g y₀ ∙' k-pt
          lemma idp = ∙-unit-r _ ∙ f.adj _

      from-to : {Y = Y₁ : Ptd j} (⊙e₁ : _⊙≃_ {i} {j} X Y₁)
                (k₁ : _⊙→_ {k} {i} Z X) →
                _==_ {lmax i k}
                {Σ {lmax i k} {i} (de⊙ Z → de⊙ X)
                (λ f → _==_ {i} {de⊙ X} (f (pt Z)) (pt X))}
                (_⊙∘_ {k} {j} {i} {Z} {Y₁} {X} (⊙<– {i} {j} {X} {Y₁} ⊙e₁)
                (_⊙∘_ {k} {i} {j} {Z} {X} {Y₁} (⊙–> {i} {j} {X} {Y₁} ⊙e₁) k₁))
                k₁
      from-to ((f , idp) , f-ise) (k , idp) = ⊙λ=' (f.g-f ∘ k) $ ↓-idf=cst-in' idp
        where module f = is-equiv {i} {j} f-ise

  post⊙∘-equiv : (Z ⊙→ X) ≃ (Z ⊙→ Y)
  post⊙∘-equiv = _ , post⊙∘-is-equiv

  pre⊙∘-is-equiv : is-equiv (λ (k : Y ⊙→ Z) → k ⊙∘ ⊙–> ⊙e)
  pre⊙∘-is-equiv = is-eq (_⊙∘ ⊙–> ⊙e) (_⊙∘ ⊙<– ⊙e) (to-from ⊙e) (from-to ⊙e) where
    abstract
      to-from : {Z = Z₁ : Ptd k} (⊙e₁ : _⊙≃_ {i} {j} X Y)
                (k₁ : _⊙→_ {i} {k} X Z₁) →
                _==_ {lmax i k}
                {Σ {lmax i k} {k} (de⊙ X → de⊙ Z₁)
                (λ f → _==_ {k} {de⊙ Z₁} (f (pt X)) (pt Z₁))}
                (_⊙∘_ {i} {j} {k} {X} {Y} {Z₁}
                (_⊙∘_ {j} {i} {k} {Y} {X} {Z₁} k₁ (⊙<– {i} {j} {X} {Y} ⊙e₁))
                (⊙–> {i} {j} {X} {Y} ⊙e₁))
                k₁
      to-from ((f , idp) , f-ise) (k , idp) = ⊙λ=' (ap k ∘ f.g-f) $ ↓-idf=cst-in' $ ∙-unit-r _
        where module f = is-equiv f-ise

      from-to : {Z = Z₁ : Ptd k} (⊙e₁ : _⊙≃_ {i} {j} X Y)
                (k₁ : _⊙→_ {j} {k} Y Z₁) →
                _==_ {lmax j k}
                {Σ {lmax j k} {k} (de⊙ Y → de⊙ Z₁)
                (λ f → _==_ {k} {de⊙ Z₁} (f (pt Y)) (pt Z₁))}
                (_⊙∘_ {j} {i} {k} {Y} {X} {Z₁}
                (_⊙∘_ {i} {j} {k} {X} {Y} {Z₁} k₁ (⊙–> {i} {j} {X} {Y} ⊙e₁))
                (⊙<– {i} {j} {X} {Y} ⊙e₁))
                k₁
      from-to ((f , idp) , f-ise) (k , idp) = ⊙λ=' (ap k ∘ f.f-g) $ ↓-idf=cst-in' $
        ∙-unit-r _ ∙ ap-∘ k f (f.g-f (pt X)) ∙ ap (ap k) (f.adj (pt X))
        where module f = is-equiv f-ise

  pre⊙∘-equiv : (Y ⊙→ Z) ≃ (X ⊙→ Z)
  pre⊙∘-equiv = _ , pre⊙∘-is-equiv

  pre⊙∘-hfib-contr : (g : X ⊙→ Z) → is-contr (Σ (Y ⊙→ Z) (λ k → (k ⊙∘ ⊙–> ⊙e) ⊙-comp g))
  pre⊙∘-hfib-contr g =
    equiv-preserves-level (Σ-emap-r (λ _ → ⊙-comp-==-≃)) {{equiv-is-contr-map (pre⊙∘-is-equiv) g}}

module _ {i j} {X : Ptd i} {Y : Ptd j} (⊙e : X ⊙≃ Y) where

  linv⊙-unique : {f₁ f₂ : Y ⊙→ X} → (f₁ ⊙∘ ⊙–> ⊙e) ⊙-comp ⊙idf X → (f₂ ⊙∘ ⊙–> ⊙e) ⊙-comp ⊙idf X → f₁ == f₂
  linv⊙-unique {f₁} {f₂} p₁ p₂ = fst= (contr-has-all-paths {{pre⊙∘-hfib-contr ⊙e (⊙idf X)}} (f₁ , p₁) (f₂ , p₂))

-- induction principle for ⊙≃

module _ {i} {X : Ptd i} where
 
  ⊙≃-contr-aux :
    is-contr
      (Σ (Σ (Type i) (λ A → de⊙ X ≃ A)) (λ (A , e) → Σ A (λ a₀ → fst e (pt X) == a₀)))
  ⊙≃-contr-aux =
    equiv-preserves-level
      ((Σ-contr-red
        {P = λ (A , e) → Σ A (λ a₀ → fst e (pt X) == a₀)} ≃-tot-contr)⁻¹)
      {{pathfrom-is-contr-instance}}

  abstract
    ⊙≃-contr : is-contr (Σ (Ptd i) (λ Y → X ⊙≃ Y))
    ⊙≃-contr = equiv-preserves-level lemma {{⊙≃-contr-aux}}
      where
        lemma :
          Σ (Σ (Type i) (λ A → de⊙ X ≃ A)) (λ (A , e) → Σ A (λ a₀ → fst e (pt X) == a₀))
            ≃
          Σ (Ptd i) (λ Y → X ⊙≃ Y)
        lemma =
          equiv
            (λ ((A , e) , (a , p)) → ⊙[ A , a ] , ≃-to-⊙≃ e p)
            (λ (Y , ⊙e) → ((de⊙ Y) , (⊙≃-to-≃ ⊙e)) , ((pt Y) , (⊙–>-pt ⊙e)))
            (λ (Y , ⊙e) → idp)
            λ ((A , e) , (a , p)) → idp

  ⊙≃-ind : ∀ {k} (P : (Y : Ptd i) → (X ⊙≃ Y → Type k))
    → P X (⊙ide X) → {Y : Ptd i} (e : X ⊙≃ Y) → P Y e
  ⊙≃-ind P = ID-ind-map P ⊙≃-contr

module _ {i} {X : Ptd i} {Y : Ptd i} where

  ⊙≃-to-== : X ⊙≃ Y → X == Y 
  ⊙≃-to-== = ⊙≃-ind {X = X} (λ Y _ → X == Y) idp

{- Pointed maps out of bool -}

-- intuition : [f true] is fixed and the only changable part is [f false].

⊙Bool→-to-idf : ∀ {i} {X : Ptd i}
  → ⊙Bool ⊙→ X → de⊙ X
⊙Bool→-to-idf (h , _) = h false

⊙Bool→-equiv-idf : ∀ {i} (X : Ptd i)
  → (⊙Bool ⊙→ X) ≃ de⊙ X
⊙Bool→-equiv-idf {i} X = equiv ⊙Bool→-to-idf g f-g g-f
  where
  g : de⊙ X → ⊙Bool ⊙→ X
  g x = Bool-rec (pt X) x , idp

  abstract
    f-g : ∀ x → ⊙Bool→-to-idf (g x) == x
    f-g x = idp

    g-f : ∀ H → g (⊙Bool→-to-idf H) == H
    g-f (h , hpt) = pair=
      (λ= lemma)
      (↓-app=cst-in $
        idp
          =⟨ ! (!-inv-l hpt) ⟩
        ! hpt ∙ hpt
          =⟨ ! (app=-β lemma true) |in-ctx (λ w → w ∙ hpt) ⟩
        app= (λ= lemma) true ∙ hpt
          =∎)
      where lemma : ∀ b → fst (g (h false)) b == h b
            lemma true = ! hpt
            lemma false = idp

⊙Bool→-equiv-idf-nat : ∀ {i j} {X : Ptd i} {Y : Ptd j} (F : X ⊙→ Y)
  → CommSquareEquiv
      (F ⊙∘_)
      (fst F)
      ⊙Bool→-to-idf
      ⊙Bool→-to-idf
⊙Bool→-equiv-idf-nat F = (comm-sqr λ _ → idp) ,
  snd (⊙Bool→-equiv-idf _) , snd (⊙Bool→-equiv-idf _)
