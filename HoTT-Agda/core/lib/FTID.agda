{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Sigma
open import lib.types.Pi

module lib.FTID where

-- Identity system and associated induction principle

module _ {i j} (A : Type i) (B : A → Type j) (a : A) (b : B a) where

  ID-sys : Type (lmax i j)
  ID-sys = (p : Σ A B) → (a , b) == p

  module _ {k} (P : (x : A) → (B x → Type k)) where

    depEval : ((x : A) → ((y : B x) → P x y)) → P a b
    depEval h = h a b

    module _ (s : ID-sys) where

      const-dp : (p : P a b) → transport (λ (x , y) → P x y) (s (a , b)) p == p
      const-dp p = transpFunEq lemma p where
        lemma : s (a , b) == idp
        lemma = Set-UIP (contr-is-set (has-level-in ((a , b) , s))) (s (a , b)) idp

      fib-pr-eq : (x : A) (y : B x) → P a b → P x y
      fib-pr-eq x y = transport (λ (x , y) → P x y) (s (x , y)) 

      ID-sys-ind : has-sec {f = depEval}
      ID-sys-ind = sect (λ z x y → fib-pr-eq x y z) const-dp

module _ {i j k} {A : Type i} {B : A → Type j} {a : A} {b : B a} (P : (x : A) → (B x → Type k)) where

  ID-ind : ID-sys A B a b → has-sec {f = depEval A B a b P}
  ID-ind s = ID-sys-ind A B a b P s

  module _ (σ : is-contr (Σ A B)) where

    private
      tot-cent : ID-sys A B a b
      tot-cent r = ! (contr-path σ (a , b)) ∙ contr-path σ r

    ID-ind-map : P a b → {x : A} (d : B x) → P x d
    ID-ind-map r {a} p = ind (ID-ind tot-cent) r a p

    ID-ind-map-β : (r : P a b) → ID-ind-map r b == r 
    ID-ind-map-β r = ind-eq (ID-ind tot-cent) r

module _ {i} {A : Type i} where

  ≃-tot-contr : is-contr (Σ (Type i) (λ B → A ≃ B))
  ≃-tot-contr = equiv-preserves-level (Σ-emap-r (λ B → ua-equiv ⁻¹)) {{pathfrom-is-contr A}}

  equiv-induction-b : ∀ {k} (P : {B : Type i} → (A ≃ B → Type k))
    → P (ide A) → {B : Type i} (e : A ≃ B) → P e
  equiv-induction-b P = ID-ind-map (λ B → P {B}) ≃-tot-contr

  equiv-induction-β : ∀ {k} {P : {B : Type i} → (A ≃ B → Type k)} (r : P (ide A))
    → equiv-induction-b P r (ide A) == r
  equiv-induction-β {P = P} = ID-ind-map-β (λ B → P {B}) ≃-tot-contr

-- induction principle arising from funext

module _ {i j} {A : Type i} {B : A → Type j} {f : Π A B} where

  funhom-contr : is-contr (Σ (Π A B) (λ g → f ∼ g))
  funhom-contr = equiv-preserves-level (Σ-emap-r (λ g → app=-equiv)) {{pathfrom-is-contr f}}

  ∼-ind : ∀ {k} (P : (g : Π A B) → (f ∼ g → Type k))
    → P f (λ x → idp) → (g : Π A B) (p : f ∼ g) → P g p
  ∼-ind P r g p = ID-ind-map P funhom-contr r {g} p

  ∼-ind-β : ∀ {k} {P : (g : Π A B) → (f ∼ g → Type k)} (r : P f (λ x → idp))
    → ∼-ind P r f (λ x → idp) == r
  ∼-ind-β {P = P} = ID-ind-map-β P funhom-contr

  funhom-contr-to : is-contr (Σ (Π A B) (λ g → g ∼ f))
  funhom-contr-to = equiv-preserves-level (Σ-emap-r (λ g → app=-equiv)) {{pathto-is-contr f}}

≃-∼-tot-contr : ∀ {i j} {A : Type i} {f : A → Type j}
  → is-contr (Σ (A → Type j) (λ g → (x : A ) → f x ≃ g x))
≃-∼-tot-contr {f} = equiv-preserves-level (Σ-emap-r (λ g → Π-emap-r λ _ → ua-equiv ⁻¹)) {{funhom-contr}}

module _ {i j} {A : Type i} {B : A → Type j} {f : Π A B} where

  funhom-contr-∼ : {g : Π A B} → f ∼ g → is-contr (Σ (Π A B) (λ h → f ∼ h))
  funhom-contr-∼ {g} H = has-level-in
    ((g , H) , uncurry (∼-ind {f = f} (λ h p → _) (! (contr-path funhom-contr (g , H)))))

module _ {i j l} {A : Type i} {B : Type j} {C : Type l} {f g : A → B} where

  pre∘-λ= : (h : C → A) (H : f ∼ g) → ap (λ k z → k (h z)) (λ= H) == λ= (λ z → H (h z))
  pre∘-λ= h = ∼-ind {B = λ _ → B} (λ g H → ap (λ k z → k (h z)) (λ= H) == λ= (λ z → H (h z))) aux g
    where
      aux : ap (λ k z → k (h z)) (λ= (λ x → idp)) == λ= (λ z → idp)
      aux =
        ap (λ k z → k (h z)) (λ= (λ x → idp))
          =⟨ ap (ap (λ k z → k (h z))) (! (λ=-η idp) ) ⟩
        idp
          =⟨ λ=-η idp ⟩
        λ= (λ z → idp) =∎

  post∘-λ= : (h : B → C) (H : f ∼ g) → ap (λ k z → h (k z)) (λ= H) == λ= (λ z → ap h (H z))
  post∘-λ= h = ∼-ind {B = λ _ → B} (λ g H → ap (λ k z → h (k z)) (λ= H) == λ= (λ z → ap h (H z))) aux g
    where
      aux : ap (λ k z → h (k z)) (λ= (λ x → idp)) == λ= (λ z → idp)
      aux =
        ap (λ k z → h (k z)) (λ= (λ x → idp))
          =⟨ ap (ap (λ k z → h (k z))) (! (λ=-η idp) ) ⟩
        idp
          =⟨ λ=-η idp ⟩
        λ= (λ z → idp) =∎

module _ {i j l} {A : Type i} {B : Type j} {C : Type l} {f : A → B → C} where

  ap-λ=-curr : {a₁ a₂ : A} (p : a₁ == a₂)
    → ap f p == λ= (λ z → ap (λ v → f v z) p) 
  ap-λ=-curr idp = λ=-η idp
