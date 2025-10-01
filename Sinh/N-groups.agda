{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.FTID
open import lib.NConnected
open import lib.NType2
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.TLevel
open import lib.types.Truncation
open import lib.types.Pointed
open import lib.types.Paths

-- two equivalent ways of describing n-groups as synthetic higher groups

module N-groups where

[_,_]-Groups : (n : ℕ) (i : ULevel) → Type (lsucc i)
[ n , i ]-Groups = Σ (Ptd i) (λ X → is-connected 0 (de⊙ X) × has-level ⟨ n ⟩ (de⊙ X))

[_,_]-conn-trunc : (n : ℕ) (i : ULevel) → Type (lsucc i)
[ n , i ]-conn-trunc = Σ (Type i) (λ X → is-connected ⟨ n ⟩ X × has-level ⟨ S n ⟩ X)

[_,_,_]-Groups-v2 : (n : ℕ) (i j : ULevel) → Type (lmax (lsucc i) (lsucc j))
[ n , i , j ]-Groups-v2 = [ BG ∈ [ n , i ]-Groups ] × [ F ∈ (de⊙ (fst BG) →  [ n , j ]-conn-trunc) ] × fst (F (pt (fst BG)))

NGroups-== : ∀ {i} {n} {G₁ G₂ : [ n , i ]-Groups} → (fst G₁ ⊙≃ fst G₂) ≃ (G₁ == G₂)
NGroups-== {n = n} {G₁} {G₂} =
  Subtype=-econv (subtypeprop (λ X → is-connected 0 (de⊙ X) × has-level ⟨ n ⟩ (de⊙ X))) G₁ G₂ ∘e (⊙≃-ua {X = fst G₁} {fst G₂}) ⁻¹

NGroups-==-contr : ∀ {i} {n} (G₁ : [ n , i ]-Groups) → is-contr (Σ  [ n , i ]-Groups (λ G₂ → fst G₁ ⊙≃ fst G₂))
NGroups-==-contr G₁ = equiv-preserves-level ((Σ-emap-r (λ _ → NGroups-==)) ⁻¹) {{pathfrom-is-contr G₁}}

Type-conn-trunc-== : ∀ {i} {n} {G₁ G₂ : [ n , i ]-conn-trunc} → (fst G₁ ≃ fst G₂) ≃ (G₁ == G₂)
Type-conn-trunc-== {n = n} {G₁} {G₂} =
  Subtype=-econv (subtypeprop (λ X → is-connected ⟨ n ⟩ X × has-level ⟨ S n ⟩ X)) G₁ G₂ ∘e ua-equiv {A = fst G₁} {fst G₂}

Type-conn-trunc-==-contr : ∀ {i} {n} (G₁ : [ n , i ]-conn-trunc) → is-contr (Σ [ n , i ]-conn-trunc (λ G₂ → fst G₁ ≃ fst G₂))
Type-conn-trunc-==-contr G₁ = equiv-preserves-level ((Σ-emap-r (λ _ → Type-conn-trunc-==)) ⁻¹) {{pathfrom-is-contr G₁}}

module NG-eql (n : ℕ) (i j : ULevel) where

  _NG-v2-==_ : [ n , i , j ]-Groups-v2 → [ n , i , j ]-Groups-v2 → Type (lmax i j)
  _NG-v2-==_ (BG₁ , F₁ , p₁) (BG₂ , F₂ , p₂) =
    [ (e , _) ∈ fst BG₁ ⊙≃ fst BG₂ ] ×
      [ t ∈ Π (de⊙ (fst BG₁)) (λ b → fst (F₁ b) ≃ fst (F₂ (fst e b))) ] ×
        (transport (fst ∘ F₂) (snd e) (–> (t (pt (fst BG₁))) p₁) == p₂)

  NG-v2-idp : (G : [ n , i , j ]-Groups-v2) → G NG-v2-== G
  fst (NG-v2-idp (BG , F , p)) = ⊙ide (fst BG)
  fst (snd (NG-v2-idp (BG , F , p))) b = ide (fst (F b))
  snd (snd (NG-v2-idp (BG , F , p))) = idp

  module _ {BG@(BG₁ , F₁ , p₁) : [ n , i , j ]-Groups-v2} where

    private
      θ = 
        Σ (Σ [ n , i ]-Groups (λ BG₂ → fst BG₁ ⊙≃ fst BG₂)) (λ (BG₂ , e , _) →
          Σ (Σ (de⊙ (fst BG₂) →  [ n , j ]-conn-trunc) (λ F₂ → Π (de⊙ (fst BG₁)) (λ b → fst (F₁ b) ≃ fst (F₂ (fst e b))))) (λ (F₂ , t) →
            Σ (fst (F₂ (pt (fst BG₂)))) (λ p₂ → transport (fst ∘ F₂) (snd e) (–> (t (pt (fst BG₁))) p₁) == p₂)))

    NG-v2-contr-aux : is-contr θ
    NG-v2-contr-aux =
      equiv-preserves-level
        ((Σ-contr-red {A = Σ [ n , i ]-Groups (λ BG₂ → fst BG₁ ⊙≃ fst BG₂)} (NGroups-==-contr BG₁))⁻¹)
        {{equiv-preserves-level
          ((Σ-contr-red (equiv-preserves-level choice {{Π-level λ x → Type-conn-trunc-==-contr (F₁ x)}}))⁻¹)
          {{pathfrom-is-contr p₁}}}}

    abstract
      NG-v2-contr : is-contr (Σ [ n , i , j ]-Groups-v2 (λ BG₂ → BG NG-v2-== BG₂))
      NG-v2-contr = equiv-preserves-level lemma {{NG-v2-contr-aux}}
        where
          lemma : θ ≃ Σ [ n , i , j ]-Groups-v2 (λ BG₂ → BG NG-v2-== BG₂)
          lemma =
            equiv
              (λ ((BG , e) , (F , t) , p , c) → (BG , F , p) , (e , t , c))
              (λ ((BG , F , p) , (e , t , c)) → (BG , e) , ((F , t) , (p , c)))
              (λ _ → idp)
              λ _ → idp

    NG-v2-ind : ∀ {k} (P : (BG₂ : [ n , i , j ]-Groups-v2) → (BG NG-v2-== BG₂ → Type k))
      → P BG (NG-v2-idp BG) → {BG₂ : [ n , i , j ]-Groups-v2} (e : BG NG-v2-== BG₂) → P BG₂ e
    NG-v2-ind P = ID-ind-map P NG-v2-contr

  abstract
    NG-v2-to-== : {BG₁ BG₂ : [ n , i , j ]-Groups-v2} → BG₁ NG-v2-== BG₂ → BG₁ == BG₂ 
    NG-v2-to-== {BG₁} = NG-v2-ind (λ BG₂ _ → BG₁ == BG₂) idp

module _ {n : ℕ} {i : ULevel} where

  open NG-eql n i i

  private    

    to : [ S n , i ]-Groups → [ n , i , i ]-Groups-v2
    fst (fst (to (X , cX , tX))) = ⊙Trunc ⟨ n ⟩ X
    fst (snd (fst (to (X , cX , tX)))) = Trunc-preserves-conn cX
    snd (snd (fst (to (X , cX , tX)))) = ⟨⟩
    fst (snd (to (X , cX , tX))) b = (hfiber [_] b) , conn-[ b ] , (Σ-level tX λ _ → =-preserves-level (raise-level ⟨ n ⟩ ⟨⟩))
    snd (snd (to (X , cX , tX))) = (pt X) , idp
  
    from : [ n , i , i ]-Groups-v2 → [ S n , i ]-Groups
    fst (from ((BG , cBG , tBG) , F , p)) = ⊙[ (Σ (de⊙ BG) (fst ∘ F)) , ((pt BG) , p) ]
    fst (snd (from ((BG , cBG , tBG) , F , p))) = Σ-conn cBG λ x → connected-≤T 0≤T {{fst (snd (F x))}}
    snd (snd (from ((BG , cBG , tBG) , F , p))) = Σ-level (raise-level _ tBG) λ x → snd (snd (F x))

    abstract

      base-≃ : (((BG , cBG , tBG) , F , p) : [ n , i , i ]-Groups-v2) → Trunc ⟨ n ⟩ (Σ (de⊙ BG) (λ z → fst (F z))) ≃ de⊙ BG
      base-≃ ((BG , cBG , tBG) , F , p) = unTrunc-equiv _ {{tBG}} ∘e Trunc-emap (Σ-contr-red-cod {{λ {x} → fst (snd (F x))}}) ∘e Trunc-Σ

      to-from : (G : [ n , i , i ]-Groups-v2) → to (from G) == G
      to-from G@((BG , cBG , tBG) , F , p) = NG-v2-to-==
        (≃-to-⊙≃ (base-≃ G) idp ,
        ((λ x → hfiber-fst (–> (base-≃ G) x) ∘e ≃-tri-hfib (base-≃ G) (λ _ → idp) x) ,
        idp)) 

      from-to : (G : [ S n , i ]-Groups) → from (to G) == G
      from-to (X , cX , tX) = –> NGroups-== (≃-to-⊙≃ (total-hfib-≃ [_]) idp)

  N-Grps-≃ : [ S n , i ]-Groups ≃ [ n , i , i ]-Groups-v2
  N-Grps-≃ = equiv to from to-from from-to
