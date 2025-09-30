{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.FTID
open import lib.NConnected
open import lib.NType2
open import lib.types.Sigma
open import lib.types.TLevel
open import lib.types.Truncation
open import lib.types.Pointed

-- two equivalent ways of describing n-groups as synthetic higher groups

module N-groups where

[_,_]-Groups : (n : ℕ) (i : ULevel) → Type (lsucc i)
[ n , i ]-Groups = Σ (Ptd i) (λ X → is-connected 0 (de⊙ X) × has-level ⟨ n ⟩ (de⊙ X))

NGroups-== : ∀ {i} {n} {G₁ G₂ : [ n , i ]-Groups} → (fst G₁ ⊙≃ fst G₂) ≃ (G₁ == G₂)
NGroups-== {n = n} {G₁} {G₂} =
  Subtype=-econv (subtypeprop (λ X → is-connected 0 (de⊙ X) × has-level ⟨ n ⟩ (de⊙ X))) G₁ G₂ ∘e (⊙≃-ua {X = fst G₁} {fst G₂}) ⁻¹

[_,_]-conn-trunc : (n : ℕ) (i : ULevel) → Type (lsucc i)
[ n , i ]-conn-trunc = Σ (Type i) (λ X → is-connected ⟨ n ⟩ X × has-level ⟨ S n ⟩ X)

[_,_,_]-Groups-v2 : (n : ℕ) (i j : ULevel) → Type (lmax (lsucc i) (lsucc j))
[ n , i , j ]-Groups-v2 = [ BG ∈ [ n , i ]-Groups ] × [ F ∈ (de⊙ (fst BG) →  [ n , j ]-conn-trunc) ] × fst (F (pt (fst BG)))

module _ {n : ℕ} {i j : ULevel} where

  _NG-v2-==_ : [ n , i , j ]-Groups-v2 → [ n , i , j ]-Groups-v2 → Type (lmax i j)
  _NG-v2-==_ (BG₁ , F₁ , p₁) (BG₂ , F₂ , p₂) =
    [ (e , _) ∈ fst BG₁ ⊙≃ fst BG₂ ] ×
      [ t ∈ Π (de⊙ (fst BG₁)) (λ b → fst (F₁ b) ≃ fst (F₂ (fst e b))) ] ×
        (transport (fst ∘ F₂) (snd e) (–> (t (pt (fst BG₁))) p₁) == p₂)

  NG-v2-idp : (G : [ n , i , j ]-Groups-v2) → G NG-v2-== G
  fst (NG-v2-idp (BG , F , p)) = ⊙ide (fst BG)
  fst (snd (NG-v2-idp (BG , F , p))) b = ide (fst (F b))
  snd (snd (NG-v2-idp (BG , F , p))) = idp

module _ {n : ℕ} {i : ULevel} where

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
