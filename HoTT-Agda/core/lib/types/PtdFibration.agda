{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.NConnected
open import lib.FTID
open import lib.NType2
open import lib.Equivalence2
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Pointed
open import lib.types.LoopSpace
open import lib.types.TLevel
open import lib.types.Paths

-- pointed sections of pointed type families

module lib.types.PtdFibration where

module _ {i j} (X : Ptd i)  where

  -- type of pointed sections
  Π⊙ : (Y : de⊙ X → Type j) → Y (pt X) → Type (lmax i j)
  Π⊙ Y p = [ s ∈ Π (de⊙ X) Y ] × (s (pt X) == p)

module _ {i j k} {X : Ptd i} where

  infixr 50 ⟨_&_⟩Π⊙-==⟨_&_⟩
  ⟨_&_⟩Π⊙-==⟨_&_⟩ : (Y₁ : de⊙ X → Type j) → Y₁ (pt (X)) → (Y₂ : de⊙ X → Type k) → Y₂ (pt X) → Type (lmax (lmax i j) k)
  ⟨ Y₁ & p₁ ⟩Π⊙-==⟨ Y₂ & p₂ ⟩ = Σ ((x : de⊙ X) → Y₁ x ≃ Y₂ x) (λ e → –> (e (pt X)) p₁ == p₂)

  Π⊙-==-ext : ∀ {Y₁ p₁ Y₂ p₂} → ⟨ Y₁ & p₁ ⟩Π⊙-==⟨ Y₂ & p₂ ⟩ → Π⊙ X Y₁ p₁ ≃ Π⊙ X Y₂ p₂
  Π⊙-==-ext {p₁ = p₁} {p₂ = p₂} (f , p) = Σ-emap-l (λ s → s (pt X) == p₂) (Π-emap-r λ x → f x) ∘e Σ-emap-r λ s →
    post∙-equiv p ∘e ap-equiv (f (pt X)) _ _

-- SIP for pointed sections

module _ {i j} {X : Ptd i} where

  infixr 50 ⟨_&_⟩_⊙Π∼_
  ⟨_&_⟩_⊙Π∼_ : (Y : de⊙ X → Type j) (p : Y (pt X)) → Π⊙ X Y p → Π⊙ X Y p → Type (lmax i j)
  ⟨ Y & p ⟩ f₁ ⊙Π∼ f₂ = [ H ∈ fst f₁ ∼ fst f₂ ] × (H (pt X) == snd f₁ ∙' ! (snd f₂)) 

  ⊙Π∼-id : (Y : de⊙ X → Type j) (p : Y (pt X)) (f : Π⊙ X Y p) → ⟨ Y & p ⟩ f ⊙Π∼ f
  ⊙Π∼-id _ _ f = (λ _ → idp) , ! (!-inv'-r (snd f))

module _ {i j} {X : Ptd i} {Y : de⊙ X → Type j} {p : Y (pt X)} (f : Π⊙ X Y p) where

  ⊙Π-contr-aux :
    is-contr
      (Σ (Σ (Π (de⊙ X) Y) (λ g → fst f ∼ g))
        (λ (h , K) → Σ (h (pt X) == p) (λ q → (K (pt X) == snd f ∙' ! q))))
  ⊙Π-contr-aux =
    equiv-preserves-level
      ((Σ-contr-red
        {A = Σ (Π (de⊙ X) Y) (λ g → fst f ∼ g)}
        (funhom-contr {f = fst f}))⁻¹)
        {{equiv-preserves-level ((Σ-emap-r (λ q → aux (snd f) q)) ⁻¹)}}
        where
          aux : {x y : Y (pt X)} (q₁ q₂ : x == y) → (idp == q₁ ∙' ! q₂) ≃ (q₂ == q₁)
          aux q₁ idp = ide (idp == q₁)

  abstract
    ⊙Π-contr : is-contr (Σ (Π⊙ X Y p) (λ g → ⟨ Y & p ⟩ f ⊙Π∼ g))
    ⊙Π-contr = equiv-preserves-level lemma {{⊙Π-contr-aux}}
      where
        lemma :
          Σ (Σ (Π (de⊙ X) Y) (λ g → fst f ∼ g))
            (λ (h , K) → Σ (h (pt X) == p) (λ q → (K (pt X) == snd f ∙' ! q)))
            ≃
          Σ (Π⊙ X Y p) (λ g → ⟨ Y & p ⟩ f ⊙Π∼ g)
        lemma =
          equiv
            (λ ((g , K) , (q , H)) → (g , q) , (K , H))
            (λ ((h , q) , (H , K)) → (h , H) , (q , K))
            (λ _ → idp)
            λ _ → idp

  ⊙Π-ind : ∀ {k} (P : (g : Π⊙ X Y p) → (⟨ Y & p ⟩ f ⊙Π∼ g → Type k))
    → P f (⊙Π∼-id Y p f) → {g : Π⊙ X Y p} (p : ⟨ Y & p ⟩ f ⊙Π∼ g) → P g p
  ⊙Π-ind P = ID-ind-map P ⊙Π-contr

  ⊙Π-ind-β : ∀ {k} (P : (g : Π⊙ X Y p) → (⟨ Y & p ⟩ f ⊙Π∼ g → Type k))
    → (r : P f (⊙Π∼-id Y p f)) → ⊙Π-ind P r {f} (⊙Π∼-id Y p f) == r
  ⊙Π-ind-β P = ID-ind-map-β P ⊙Π-contr

  ⊙Π∼-to-== : {k : Π⊙ X Y p} → ⟨ Y & p ⟩ f ⊙Π∼ k → f == k
  ⊙Π∼-to-== = ⊙Π-ind (λ k _ →  f == k) idp

  ⊙Π∼-== : (g : Π⊙ X Y p) → (⟨ Y & p ⟩ f ⊙Π∼ g) ≃ (f == g)
  ⊙Π∼-== g = equiv (⊙Π∼-to-== {g}) (can {g}) can-⊙Π∼-to-== ⊙Π∼-to-==-can
    where
      can : {k : Π⊙ X Y p} → f == k → ⟨ Y & p ⟩ f ⊙Π∼ k
      can idp = ⊙Π∼-id Y p f

      can-⊙Π∼-to-== : {k : Π⊙ X Y p} (p : f == k) → ⊙Π∼-to-== (can p) == p
      can-⊙Π∼-to-== idp = ⊙Π-ind-β (λ k _ →  f == k) idp
      
      ⊙Π∼-to-==-can : {k : Π⊙ X Y p} (p : ⟨ Y & p ⟩ f ⊙Π∼ k) → can (⊙Π∼-to-== p) == p
      ⊙Π∼-to-==-can = ⊙Π-ind (λ k p → can (⊙Π∼-to-== p) == p) (ap can (⊙Π-ind-β (λ k _ →  f == k) idp))

-- truncation level of pointed sections

module _ {i j} (X : Ptd i) {n₁ : ℕ₋₂} {{_ : is-connected (S n₁) (de⊙ X)}} where

  abstract
    ptd-conn-tr-dhom-tr : (Y : de⊙ X → Type j) (p : Y (pt X)) {n₂ : ℕ₋₂}
      {{_ : {x : de⊙ X} → has-level (n₂ +2+ n₁) (Y x)}}  -- level (n₂ + (S (S n₁)))
      → has-level n₂ (Π⊙ X Y p)
    ptd-conn-tr-dhom-tr Y p {⟨-2⟩} = has-level-in $
      ψ ,
      λ k → ⊙Π∼-to-== ψ (aux k ,
        conn-extend-ptd-β (pt X) (λ x → conn-extend-ptd (pt X) Y p x == fst k x) (snd ψ ∙' ! (snd k))) 
        where
          ψ : Π⊙ X Y p
          ψ = ((conn-extend-ptd (pt X) Y p) , (conn-extend-ptd-β (pt X) Y p))

          aux : (k : Π⊙ X Y p) → conn-extend-ptd (pt X) Y p ∼ fst k
          aux k = conn-extend-ptd (pt X) (λ x → conn-extend-ptd (pt X) Y p x == fst k x) (snd ψ ∙' ! (snd k))
    has-level-apply (ptd-conn-tr-dhom-tr Y p {S n₂}) k₁ k₂ =
      equiv-preserves-level (⊙Π∼-== k₁ k₂) {{ptd-conn-tr-dhom-tr (λ x → fst k₁ x == fst k₂ x) (snd k₁ ∙' ! (snd k₂))}}

module _ {i j} (X : Ptd i) (Y : Ptd j) {n₁ : ℕ₋₂} (cX : is-connected (S n₁) (de⊙ X)) where

  ptd-conn-tr-hom-tr : ∀ {n₂} (tY : has-level (n₂ +2+ n₁) (de⊙ Y)) → has-level n₂ (X ⊙→ Y)
  ptd-conn-tr-hom-tr tY = ptd-conn-tr-dhom-tr X {{cX}} (λ _ → de⊙ Y) (pt Y) {{tY}}

module _ {i j} (X : Ptd i) (Y : Ptd j) {n₁ : ℕ₋₂}
  (cX : is-connected (S n₁) (de⊙ X)) (cY : is-connected (S n₁) (de⊙ Y)) where

  ptd-conn-tr-≃-tr : ∀ {n₂} (tY : has-level (n₂ +2+ n₁) (de⊙ Y)) (tX : has-level (n₂ +2+ n₁) (de⊙ X))
    → has-level n₂ (X ⊙≃ Y)
  ptd-conn-tr-≃-tr {⟨-2⟩} tY tX = inhab-prop-is-contr (⊙-binv-to-⊙≃ (contr-center aux-contr))
    {{Subtype-level (subtypeprop (λ (f , _) → is-equiv f)) {{contr-has-level (ptd-conn-tr-hom-tr X Y cX tY)}}}}
    where
      aux-contr : is-contr (X ⊙-binv Y)
      aux-contr = Σ-level (ptd-conn-tr-hom-tr X Y cX tY) λ f → Σ-level (ptd-conn-tr-hom-tr Y X cY tX)
         λ g → ×-level (=-preserves-level (ptd-conn-tr-hom-tr Y Y cY tY)) (=-preserves-level (ptd-conn-tr-hom-tr X X cX tX))
  ptd-conn-tr-≃-tr {S n₂} tY _ = Subtype-level (subtypeprop (λ (f , _) → is-equiv f)) {{ptd-conn-tr-hom-tr X Y cX tY}}

module _ {i j} {X : Ptd i} {n₁ n₂ : ℕ₋₂} {{cX : is-connected (S n₁) (de⊙ X)}} where

  instance
  
    ptd-conn-tr-dhom-tr-inst : {Y : de⊙ X → Type j} {p : Y (pt X)}
      {{_ : {x : de⊙ X} → has-level (n₂ +2+ n₁) (Y x)}}
      → has-level n₂ (Π⊙ X Y p)
    ptd-conn-tr-dhom-tr-inst {Y} {p} = ptd-conn-tr-dhom-tr X Y p

    ptd-conn-tr-≃-tr-inst : {Y : Ptd j} {{cY : is-connected (S n₁) (de⊙ Y)}}
      {{tY : has-level (n₂ +2+ n₁) (de⊙ Y)}} {{tX : has-level (n₂ +2+ n₁) (de⊙ X)}}
      → has-level n₂ (X ⊙≃ Y)
    ptd-conn-tr-≃-tr-inst {Y} {{cY}} {{tY}} {{tX}} = ptd-conn-tr-≃-tr X Y cX cY tY tX

  
