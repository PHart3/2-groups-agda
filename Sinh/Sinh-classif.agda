{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import HoTT
open import lib.types.N-groups
open import lib.types.PtdFibration
open import lib.types.Torsor
open import homotopy.EilenbergMacLane
open import homotopy.EM-unique
open import torsors.Delooping

-- classification (due to Owen Milner) of n-groups by Sính triples when n ≥ 2

module Sinh-classif where

open EMExplicit

module _ (n : ℕ) (i : ULevel) where

  Sinh-triples : Type (lsucc i)
  Sinh-triples =
    [ (BG , _ , _) ∈ [ n , i ]-Groups ] ×
      [ H ∈ (de⊙ BG → AbGroup i) ] ×
        Π⊙ BG (λ x → EM (H x) (S (S n))) (ptEM (H (pt (BG))) (S (S n)))

  Sinh-triples-set : Type (lsucc i)
  Sinh-triples-set = Trunc 0 $
    [ (BG , _ , _) ∈ [ n , i ]-Groups ] ×
      [ H ∈ (de⊙ BG → AbGroup i) ] ×
        Trunc 0 (Π⊙ BG (λ x → EM (H x) (S (S n))) (ptEM (H (pt (BG))) (S (S n))))
        -- this final type is cohomology with local coefficients 

module _ {n : ℕ} {i : ULevel} where

  -- [ S (S n) , i ]-Groups is defined in lib.types.N-groups
  NGrp-Sinh-≃ : [ S (S n) , i ]-Groups ≃ Sinh-triples (S n) i
  NGrp-Sinh-≃ =
    [ S (S n) , i ]-Groups
      ≃⟨ N-Grps-≃ ⟩
    [ (S n) , i , i ]-Groups-v2
      ≃⟨ orthog-contr ⟩
    Σ [ (S n) , i , i ]-Groups-v2 (λ (BG , F , p) → Π (de⊙ (fst BG))
      (λ u → Trunc -1 (fst (F u)) × Σ (AbGroup i) (λ H → Π (fst (F u)) (λ x →
        Ω^'S-abgroup n ⊙[ fst (F u) , x ] {{snd (snd (F u))}} == H))))
      ≃⟨ rearrange ⟩
    [ (X , cX , tX) ∈ [ S n , i ]-Groups ] ×
      [ F ∈ (de⊙ X → Type i) ] ×
        [ H ∈ (de⊙ X → AbGroup i) ] ×
          Π (de⊙ X) (λ u → Trunc -1 (F u) × is-connected ⟨ S n ⟩ (F u) ×
            Σ (has-level ⟨ S (S n) ⟩ (F u)) (λ tF →
              Π (F u) (λ x → Ω^'S-abgroup n (⊙[ F u , x ]) {{tF}} == H u))) ×
          F (pt X)
      ≃⟨ Σ-emap-r (λ (X , cX , tX) → Σ-emap-r (λ F → Σ-emap-r (λ H →
          ×-emap (choice ⁻¹) (ide (F (pt X))) ∘e
          sub-rearrange X cX ∘e
          ×-emap choice (ide (F (pt X)))))) ⟩
    [ (X , cX , tX) ∈ [ S n , i ]-Groups ] ×
      [ F ∈ (de⊙ X → Type i) ] ×
        [ H ∈ (de⊙ X → AbGroup i) ] ×
          Π (de⊙ X) (λ u → Trunc -1 (F u) ×
            Π (F u) (λ x → is-connected ⟨ S n ⟩ (F u) ×
              Σ (has-level ⟨ S (S n) ⟩ (F u)) (λ tF → Ω^'S-abgroup n (⊙[ F u , x ]) {{tF}} == H u))) ×
          F (pt X)
      ≃⟨ Σ-emap-r (λ _ → Σ₁-×-comm) ⟩
    [ (X , cX , tX) ∈ [ S n , i ]-Groups ] ×
      [ H ∈ (de⊙ X → AbGroup i) ] ×
        [ F ∈ (de⊙ X → Type i) ] ×
          Π (de⊙ X) (λ u → Trunc -1 (F u) ×
            Π (F u) (λ x → is-connected ⟨ S n ⟩ (F u) ×
              Σ (has-level ⟨ S (S n) ⟩ (F u)) (λ tF → Ω^'S-abgroup n (⊙[ F u , x ]) {{tF}} == H u))) ×
          F (pt X)
      ≃⟨ Σ-emap-r (λ (X , cX , tX) → Σ-emap-r (λ H → Σ-emap-r (λ F →
           ×-emap (Π-emap-r λ u → ×-emap (ide (Trunc -1 (F u)))
             (Π-emap-r (λ x → EM-Ω-==-ext n (H u) ⊙[ F u , x ])))
             (ide (F (pt X)))))) ⟩
    [ (X , cX , tX) ∈ [ S n , i ]-Groups ] ×
      [ H ∈ (de⊙ X → AbGroup i) ] ×
        [ F ∈ (de⊙ X → Type i) ] ×
          Π (de⊙ X) (λ u → Trunc -1 (F u) ×
            Π (F u) (λ x → ⊙EM (H u) (S (S n)) ⊙≃ ⊙[ F u , x ])) ×
          F (pt X)
      ≃⟨ Σ-emap-r (λ (X , cX , tX) → Σ-emap-r (λ H → Σ-emap-r (λ F →
           Σ-emap-r (λ _ → tors-ptd-is-trivial (⊙EM (H (pt X)) (S (S n)))
             {{PtdTorsors-contr {{EM-conn (H (pt X))}}}})))) ⟩
    [ (X , cX , tX) ∈ [ S n , i ]-Groups ] ×
      [ H ∈ (de⊙ X → AbGroup i) ] ×
        [ F ∈ (de⊙ X → Type i) ] ×
          [ d ∈ Π (de⊙ X) (λ u → Trunc -1 (F u) ×
            Π (F u) (λ x → ⊙EM (H u) (S (S n)) ⊙≃ ⊙[ F u , x ])) ] ×
          ((F (pt X) , d (pt X)) == pt (⊙Torsors (⊙EM (H (pt X)) (S (S n)))
            {{PtdTorsors-contr {{EM-conn (H (pt X))}}}})) 
      ≃⟨ Σ-emap-r (λ (X , cX , tX) → Σ-emap-r (λ H →
           equiv
             (λ (F , d , q) → (λ u → (F u) , ((fst (d u)) , (snd (d u)))) , q)
             (λ (trs , q) → (fst ∘ trs) , (λ u → (fst (snd (trs u))) , snd (snd (trs u))) , q)
             (λ _ → idp) λ _ → idp)) ⟩
    [ (X , cX , tX) ∈ [ S n , i ]-Groups ] ×
      [ H ∈ (de⊙ X → AbGroup i) ] ×
          Π⊙ X (λ u → Torsors i (⊙EM (H u) (S (S n))))
            (pt (⊙Torsors (⊙EM (H (pt X)) (S (S n))) {{PtdTorsors-contr {{EM-conn (H (pt X))}}}}))
      ≃⟨ Σ-emap-r (λ (X , cX , tX) →
           Σ-emap-r (λ H → Π⊙-==-ext ((λ u → (EM-Torsors-≃ (H u)) ⁻¹) , ptdness X H))) ⟩
    [ (X , cX , tX) ∈ [ S n , i ]-Groups ] ×
      [ H ∈ (de⊙ X → AbGroup i) ] ×
        Π⊙ X (λ u → EM (H u) (S (S (S n)))) (ptEM (H (pt X)) (S (S (S n)))) ≃∎
      module Sinh-classif-lemmas where

        -- proof of pointedness in final equivalence
        ptdness : (X : Ptd i) (H : de⊙ X → AbGroup i) →
          fst (⊙–> (⊙EM-Torsors-≃ (H (pt X)) ⊙⁻¹))
            (pt (⊙Torsors (⊙EM (H (pt X)) (S (S n))) {{PtdTorsors-contr {{EM-conn (H (pt X))}}}}))
            ==
          pt (⊙EM (H (pt X)) (S (S (S n))))
        ptdness X H = ⊙–>-pt (⊙EM-Torsors-≃ (H (pt X)) {n} ⊙⁻¹)

        -- the second equivalence: adding singletons 
        orthog-contr :
          [ (S n) , i , i ]-Groups-v2
            ≃
          Σ [ (S n) , i , i ]-Groups-v2 (λ (BG , F , p) → Π (de⊙ (fst BG))
            (λ u → Trunc -1 (fst (F u)) × Σ (AbGroup i) (λ H → Π (fst (F u)) (λ x →
              Ω^'S-abgroup n ⊙[ fst (F u) , x ] {{snd (snd (F u))}} == H))))
        orthog-contr = 
          (Σ-contr-red-cod {{λ {(BG , F , p)} → Π-level (λ u → ×-level
          (inhab-prop-is-contr (prop-over-connected {{fst (snd BG)}} (λ u → Trunc -1 (fst (F u)) ,
            Trunc-level) [ p ] u))
          (orthog-conn-trunc (λ x → Ω^'S-abgroup n ⊙[ fst (F u) , x ] {{snd (snd (F u))}})
            (connected-≤T (≤T-ap-S 0≤T) {{fst (snd (F u))}}) AbGrp-isGrpd))}})⁻¹

        rearrange :
          (Σ [ (S n) , i , i ]-Groups-v2 (λ (BG , F , p) → Π (de⊙ (fst BG))
            (λ u → Trunc -1 (fst (F u)) × Σ (AbGroup i) (λ H → Π (fst (F u)) (λ x →
              Ω^'S-abgroup n ⊙[ fst (F u) , x ] {{snd (snd (F u))}} == H)))))
            ≃
          ([ (X , cX , tX) ∈ [ S n , i ]-Groups ] ×
            [ F ∈ (de⊙ X → Type i) ] ×
              [ H ∈ (de⊙ X → AbGroup i) ] ×
                Π (de⊙ X) (λ u → Trunc -1 (F u) × is-connected ⟨ S n ⟩ (F u) ×
                  Σ (has-level ⟨ S (S n) ⟩ (F u)) (λ tF → 
                    Π (F u) (λ x → Ω^'S-abgroup n (⊙[ F u , x ]) {{tF}} == H u))) ×
                F (pt X))
        rearrange = equiv
          (λ ((BG , F , p) , m) → BG , (fst ∘ F , ((λ u → fst (snd (m u))) , ((λ u → (fst (m u)) ,
            (fst (snd (F u))) , ((snd (snd (F u))) , (λ x → snd (snd (m u)) x))) , p))))
          (λ (BG@(X , cX , tX) , F , H , m , p) →
            (BG , ((λ u → (F u) , (fst (snd (m u)) , fst (snd (snd (m u))))) , p)) ,
              λ u → (fst (m u)) , ((H u) , (λ x → snd (snd (snd (m u))) x)))
          (λ _ → idp)
          λ _ → idp

        sub-rearrange : (X : Ptd i) (cX : is-connected 0 (de⊙ X))
          {F : de⊙ X → Type i} {H : de⊙ X → AbGroup i} →
          Σ (Π (de⊙ X) (λ z → Trunc -1 (F z))) (λ _ →
            Π (de⊙ X) (λ u → is-connected ⟨ S n ⟩ (F u) ×
              Σ (has-level ⟨ S (S n) ⟩ (F u))
                (λ tF → Π (F u) (λ x → Ω^'S-abgroup n ⊙[ F u , x ] {{tF}} == H u)))) ×
          F (pt X)
            ≃
          Σ (Π (de⊙ X) (λ z → Trunc -1 (F z))) (λ _ →
            Π (de⊙ X) (λ u → Π (F u) (λ x →
              is-connected ⟨ S n ⟩ (F u) ×
              Σ (has-level ⟨ S (S n) ⟩ (F u)) (λ tF → Ω^'S-abgroup n ⊙[ F u , x ] {{tF}} == H u)))) ×
          F (pt X)
        sub-rearrange X cX {F} {H} =
          equiv
            (λ ((t , m) , p) → (t , (λ u x → fst (m u) , fst (snd (m u)) , snd (snd (m u)) x)) , p)
            (λ ((t , m) , p) →
              (t ,
              (λ u →
                (prop-over-connected {{cX}} (λ x → is-connected ⟨ S n ⟩ (F x) , ⟨⟩)
                  (fst (m (pt X) p)) u) ,
                ((prop-over-connected {{cX}} (λ x → has-level ⟨ S (S n) ⟩ (F x) , ⟨⟩)
                  (fst (snd (m (pt X) p))) u) ,
                (λ x → ap (λ tr → Ω^'S-abgroup n ⊙[ F u , x ] {{tr}})
                  (prop-has-all-paths _ _) ∙'
                snd (snd (m u x)))))) , p)
            (λ ((t , m) , p) →
              pair×= (pair×= idp (λ= (λ u → λ= (λ x → pair×= (prop-has-all-paths _ _)
                (pair= (prop-has-all-paths _ _) (↓-app=cst-in'
                  (ap (λ q → ap (λ tr → Ω^'S-abgroup n ⊙[ F u , x ] {{tr}}) q ∙' snd (snd (m u x)))
                    (prop-has-all-paths {{=-preserves-level ⟨⟩}} _ _))))))))
                idp)
            λ ((t , m) , p) → pair×= (pair×= idp (λ= (λ u → pair×= (prop-has-all-paths _ _)
              (pair= (prop-has-all-paths _ _) (↓-Π-cst-app-in (λ x →
                ↓-app=cst-in'
                  (ap (λ q → ap (λ tr → Ω^'S-abgroup n ⊙[ F u , x ] {{tr}}) q ∙' snd (snd (m u)) x)
                    (prop-has-all-paths {{=-preserves-level ⟨⟩}} _ _))))))))
              idp

  {- a set-truncated version recovering the classical description
     of the Postnikov invariant as a cohomology class -}

  Sinh-classif-set : Trunc 0 [ S (S n) , i ]-Groups ≃ Sinh-triples-set (S n) i 
  Sinh-classif-set = -- proof is by standard interaction between truncation and Σ
    Trunc-Σ ⁻¹ ∘e Trunc-emap (Σ-emap-r λ G → Trunc-Σ) ∘e Trunc-Σ ∘e Trunc-emap NGrp-Sinh-≃
