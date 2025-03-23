{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.NConnected
open import lib.FTID
open import lib.types.Paths
open import lib.types.Sigma
open import lib.types.Pointed

-- sections of fibrations of pointed types

module lib.types.PtdFibration where

module _ {i j} (X : Ptd i)  where

  -- type of pointed sections
  Π⊙ : (de⊙ X → Ptd j) → Type (lmax i j)
  Π⊙ Y = [ s ∈ Π (de⊙ X) (de⊙ ∘ Y) ] × (s (pt X) == pt (Y (pt X)) )

-- SIP for pointed sections

module _ {i j} {X : Ptd i} where

  infixr 10 ⟨_⟩_⊙Π∼_
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

  ⊙Π∼-== : (g : Π⊙ X Y) → (⟨ Y ⟩ f ⊙Π∼ g) ≃ (f == g)
  ⊙Π∼-== g = equiv (map1 {g}) (map2 {g}) map2-map1 map1-map2
    where
      map1 : {k : Π⊙ X Y} → ⟨ Y ⟩ f ⊙Π∼ k → f == k
      map1 = ⊙Π-ind (λ k _ →  f == k) idp
      
      map2 : {k : Π⊙ X Y} → f == k → ⟨ Y ⟩ f ⊙Π∼ k
      map2 idp = ⊙Π∼-id Y f

      map2-map1 : {k : Π⊙ X Y} (p : f == k) → map1 (map2 p) == p
      map2-map1 idp = ⊙Π-ind-β (λ k _ →  f == k) idp
      
      map1-map2 : {k : Π⊙ X Y} (p : ⟨ Y ⟩ f ⊙Π∼ k) → map2 (map1 p) == p
      map1-map2 = ⊙Π-ind (λ k p → map2 (map1 p) == p) (ap map2 (⊙Π-ind-β (λ k _ →  f == k) idp))
