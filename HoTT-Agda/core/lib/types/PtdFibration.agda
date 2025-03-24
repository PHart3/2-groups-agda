{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.NConnected
open import lib.FTID
open import lib.types.Sigma
open import lib.types.Pointed
open import lib.types.LoopSpace
open import lib.types.TLevel

-- sections of fibrations of pointed types

module lib.types.PtdFibration where

module _ {i j} (X : Ptd i)  where

  -- type of pointed sections
  Π⊙ : (de⊙ X → Ptd j) → Type (lmax i j)
  Π⊙ Y = [ s ∈ Π (de⊙ X) (de⊙ ∘ Y) ] × (s (pt X) == pt (Y (pt X)) )

-- SIP for pointed sections

module _ {i j} {X : Ptd i} where

  infixr 50 ⟨_⟩_⊙Π∼_
  ⟨_⟩_⊙Π∼_ : (Y : de⊙ X → Ptd j) → Π⊙ X Y → Π⊙ X Y → Type (lmax i j)
  ⟨ Y ⟩ f₁ ⊙Π∼ f₂ = [ H ∈ fst f₁ ∼ fst f₂ ] × (! (H (pt X)) ∙ snd f₁ == snd f₂) 

  ⊙Π∼-id : (Y : de⊙ X → Ptd j) (f : Π⊙ X Y) → ⟨ Y ⟩ f ⊙Π∼ f
  ⊙Π∼-id _ _ = (λ _ → idp) , idp

module _ {i j} {X : Ptd i} {Y : de⊙ X → Ptd j} (f : Π⊙ X Y) where

  ⊙Π-contr-aux :
    is-contr
      (Σ (Σ (Π (de⊙ X) (de⊙ ∘ Y)) (λ g → fst f ∼ g))
        (λ (h , K) → Σ (h (pt X) == pt (Y (pt X))) (λ p → (! (K (pt X)) ∙ snd f == p))))
  ⊙Π-contr-aux =
    equiv-preserves-level
      ((Σ-contr-red
        {A = Σ (Π (de⊙ X) (de⊙ ∘ Y)) (λ g → fst f ∼ g)}
        {P = λ (h , K) → Σ (h (pt X) == pt (Y (pt X))) (λ p → (! (K (pt X)) ∙ snd f == p))}
        (funhom-contr {f = fst f}))⁻¹)

  abstract
    ⊙Π-contr : is-contr (Σ (Π⊙ X Y) (λ g → ⟨ Y ⟩ f ⊙Π∼ g))
    ⊙Π-contr = equiv-preserves-level lemma {{⊙Π-contr-aux }}
      where
        lemma :
          Σ (Σ (Π (de⊙ X) (de⊙ ∘ Y)) (λ g → fst f ∼ g))
            (λ (h , K) → Σ (h (pt X) == pt (Y (pt X))) (λ p → (! (K (pt X)) ∙ snd f == p)))
            ≃
          Σ (Π⊙ X Y) (λ g → ⟨ Y ⟩ f ⊙Π∼ g)
        lemma =
          equiv
            (λ ((g , K) , (p , H)) → (g , p) , (K , H))
            (λ ((h , p) , (H , K)) → (h , H) , (p , K))
            (λ ((h , p) , (H , K)) → idp)
            λ ((g , K) , (p , H)) → idp

  ⊙Π-ind : ∀ {k} (P : (g : Π⊙ X Y) → (⟨ Y ⟩ f ⊙Π∼ g → Type k))
    → P f (⊙Π∼-id Y f) → {g : Π⊙ X Y} (p : ⟨ Y ⟩ f ⊙Π∼ g) → P g p
  ⊙Π-ind P = ID-ind-map P ⊙Π-contr

  ⊙Π-ind-β : ∀ {k} (P : (g : Π⊙ X Y) → (⟨ Y ⟩ f ⊙Π∼ g → Type k))
    → (r : P f (⊙Π∼-id Y f)) → ⊙Π-ind P r {f} (⊙Π∼-id Y f) == r
  ⊙Π-ind-β P = ID-ind-map-β P ⊙Π-contr

  ⊙Π∼-to-== : {k : Π⊙ X Y} → ⟨ Y ⟩ f ⊙Π∼ k → f == k
  ⊙Π∼-to-== = ⊙Π-ind (λ k _ →  f == k) idp

  ⊙Π∼-== : (g : Π⊙ X Y) → (⟨ Y ⟩ f ⊙Π∼ g) ≃ (f == g)
  ⊙Π∼-== g = equiv (⊙Π∼-to-== {g}) (can {g}) can-⊙Π∼-to-== ⊙Π∼-to-==-can
    where
      can : {k : Π⊙ X Y} → f == k → ⟨ Y ⟩ f ⊙Π∼ k
      can idp = ⊙Π∼-id Y f

      can-⊙Π∼-to-== : {k : Π⊙ X Y} (p : f == k) → ⊙Π∼-to-== (can p) == p
      can-⊙Π∼-to-== idp = ⊙Π-ind-β (λ k _ →  f == k) idp
      
      ⊙Π∼-to-==-can : {k : Π⊙ X Y} (p : ⟨ Y ⟩ f ⊙Π∼ k) → can (⊙Π∼-to-== p) == p
      ⊙Π∼-to-==-can = ⊙Π-ind (λ k p → can (⊙Π∼-to-== p) == p) (ap can (⊙Π-ind-β (λ k _ →  f == k) idp))

  ⊙Π∼-Ω : Π⊙ X (λ x → ⊙Ω ⊙[ de⊙ (Y x) , fst f x ]) ≃ (f == f)
  ⊙Π∼-Ω = 
    Π⊙ X (λ x → ⊙Ω ⊙[ de⊙ (Y x) , fst f x ])
      ≃⟨ equiv (λ k → fst k , idp-canc-l-! (snd f) (snd k)) (λ k → fst k , canc-l-!-idp (snd f) (snd k))
           (λ k → ap (λ c → fst k , c) (aux1 {k = k} (snd f) (snd k)))
           (λ k → ap (λ c → fst k , c) (aux2 {k = k} (snd f) (snd k))) ⟩
    ⟨ Y ⟩ f ⊙Π∼ f
      ≃⟨ ⊙Π∼-== f ⟩
    f == f ≃∎
    where
      aux1 : {k : ⟨ Y ⟩ f ⊙Π∼ f} {x : de⊙ (Y (pt X))}
        (p : fst f (pt X) == x) (q : ! (fst k (pt X)) ∙ p == p)
        → idp-canc-l-! p (canc-l-!-idp p q) == q
      aux1 {k} idp q = lemma q
        where
          lemma : {x : de⊙ (Y (pt X))} {r : x == x} (t : ! r ∙ idp == idp)
            → ap (λ c → ! c ∙ idp) (!-idp r (! (∙-unit-r (! r)) ∙ t)) == t
          lemma =
            !-!-∙-unit-r-ind (λ {r} t → ap (λ c → ! c ∙ idp) (!-idp r (! (∙-unit-r (! r)) ∙ t)) == t)
              (λ { idp → idp })

      aux2 : {k : Π⊙ X (λ x → ⊙Ω ⊙[ de⊙ (Y x) , fst f x ])} {x : de⊙ (Y (pt X))}
        (p : x == pt (Y (pt X))) {r : x == x} (q : r == idp)
        → canc-l-!-idp p (idp-canc-l-! p q) == q
      aux2 idp idp = idp

-- Theorem 4.2 of the paper "Higher Groups in Homotopy Type Theory"
module _ {i j} (X : Ptd i) {n₁ : TLevel} {{_ : is-connected (S n₁) (de⊙ X)}} where

  abstract
    ptd-conn-tr-dhom-tr : (Y : de⊙ X → Ptd j) {n₂ : TLevel}
      {{_ : {x : de⊙ X} → has-level (n₂ +2+ (S n₁)) (de⊙ (Y x))}}
      → has-level (S n₂) (Π⊙ X Y)
    ptd-conn-tr-dhom-tr Y {⟨-2⟩} {{trY}} =
      contr-is-prop (has-level-in (((λ x → pt (Y x)) , idp) ,
        λ k → ⊙Π∼-to-== {Y = Y} ((λ x → pt (Y x)) , idp)
          (aux k ,
            ap (λ v → ! v ∙ idp) (conn-extend-ptd-β (pt X) (λ x → pt (Y x) == fst k x) (! (snd k))) ∙
            (ap (λ v → v ∙ idp) (!-! (snd k)) ∙ ∙-unit-r (snd k)))))
        where
          aux : (k : Π⊙ X Y) → (λ x → pt (Y x)) ∼ fst k
          aux k = conn-extend-ptd (pt X) (λ x → pt (Y x) == fst k x) (! (snd k))
    ptd-conn-tr-dhom-tr Y {S n₂} =
      UIP-loops {{λ {k} → equiv-preserves-level (⊙Π∼-Ω {Y = Y} k)
        {{ptd-conn-tr-dhom-tr λ x → ⊙Ω ⊙[ de⊙ (Y x) , fst k x ]}}}}

module _ {i j} (X : Ptd i) (Y : Ptd j) {n₁ n₂ : TLevel}
  (cX : is-connected (S n₁) (de⊙ X)) (trY : has-level (n₂ +2+ (S n₁)) (de⊙ Y)) where

  abstract
    ptd-conn-tr-hom-tr : has-level (S n₂) (X ⊙→ Y)
    ptd-conn-tr-hom-tr = ptd-conn-tr-dhom-tr X {{cX}} (λ _ → Y) {{trY}}
