{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import HoTT
open import homotopy.EilenbergMacLane
open import homotopy.EM-Grp-equiv

-- uniqueness of Eilenberg-MacLane spaces

module homotopy.EM-unique where

module _ (n : ℕ) {i} (H : AbGroup i) where

  open EMExplicit

  abstract

    EM-Ω-==-aux : (G : groupal-grpd-Ab n i) → (–> (EM-Ab-equiv n) G == H) ≃ (G == <– (EM-Ab-equiv n) H)
    EM-Ω-==-aux G = equiv-adj-≃  (EM-Ab-equiv n {i}) {G} {H}

    EM-Ω-==-to : (X : Ptd i) (tX : has-level ⟨ S (S n) ⟩ (de⊙ X)) (cX : is-connected ⟨ S n ⟩ (de⊙ X))  →
      (is-connected ⟨ S n ⟩ (de⊙ X) × Σ (has-level ⟨ S (S n) ⟩ (de⊙ X)) (λ tX' → (Ω^'S-abgroup n X {{tX'}} == H)))
        ≃
      (–> (EM-Ab-equiv n) (X , tX , cX) == H)
    EM-Ω-==-to X tX cX = equiv to from rt1 rt2
      where

        to :
          (is-connected ⟨ S n ⟩ (de⊙ X) × Σ (has-level ⟨ S (S n) ⟩ (de⊙ X)) (λ tX' → (Ω^'S-abgroup n X {{tX'}} == H)))
          → (–> (EM-Ab-equiv n) (X , tX , cX) == H)
        to (cX , tX , p) = ap (λ tr → Ω^'S-abgroup n X {{tr}}) (prop-has-all-paths _ _) ∙ p

        from :
          (–> (EM-Ab-equiv n) (X , tX , cX) == H)
          → (is-connected ⟨ S n ⟩ (de⊙ X) × Σ (has-level ⟨ S (S n) ⟩ (de⊙ X)) (λ tX' → (Ω^'S-abgroup n X {{tX'}} == H)))
        from p = cX , (tX , p)

        rt1 : (p : –> (EM-Ab-equiv n) (X , tX , cX) == H) → to (from p) == p
        rt1 p = ap (λ q → q ∙ p) (ap (ap (λ tr → Ω^'S-abgroup n X {{tr}})) (prop-has-all-paths {{=-preserves-level-instance}} _ _))

        rt2 : (t : is-connected ⟨ S n ⟩ (de⊙ X) × Σ (has-level ⟨ S (S n) ⟩ (de⊙ X)) (λ tX' → Ω^'S-abgroup n X {{tX'}} == H)) → from (to t) == t
        rt2 (cX , tX' , p) = pair×= (prop-has-all-paths _ _) (pair= (prop-has-all-paths _ _) (↓-app=cst-in idp))

    EM-Ω-==-from : (X : Ptd i) (tX : has-level ⟨ S (S n) ⟩ (de⊙ X)) (cX : is-connected ⟨ S n ⟩ (de⊙ X)) →
      ((X , tX , cX) == <– (EM-Ab-equiv n) H)
        ≃
      (X == ⊙EM H (S (S n)))
    EM-Ω-==-from X tX cX = equiv fst= from rt1 rt2
      where

        from : (X == fst (<– (EM-Ab-equiv n) H)) → (X , tX , cX == <– (EM-Ab-equiv n) H)
        from p = pair= p prop-has-all-paths-↓

        rt1 : (p : X == fst (<– (EM-Ab-equiv n) H)) →  fst= (from p) == p
        rt1 p = fst=-β p prop-has-all-paths-↓

        rt2 : (p : X , tX , cX == <– (EM-Ab-equiv n) H) → from (fst= p) == p
        rt2 p = pair== {p = fst= p} idp (prop-has-all-paths {{↓-level}} _ _) ∙ ! (pair=-η p)

  EM-Ω-== : (X : Ptd i) →
    (is-connected ⟨ S n ⟩ (de⊙ X) × Σ (has-level ⟨ S (S n) ⟩ (de⊙ X)) (λ tX → (Ω^'S-abgroup n X {{tX}} == H)))
      ≃
    (X == ⊙EM H (S (S n)))
  EM-Ω-== X = equiv to from rt1 rt2 where

    to : (is-connected ⟨ S n ⟩ (de⊙ X) × Σ (has-level ⟨ S (S n) ⟩ (de⊙ X)) (λ tX → (Ω^'S-abgroup n X {{tX}} == H))) → X == ⊙EM H (S (S n))
    to t@(cX , tX , p) = –> (EM-Ω-==-from X tX cX ∘e EM-Ω-==-aux (X , tX , cX) ∘e EM-Ω-==-to X tX cX) t

    abstract
      to-invt : {c₁ c₂ : is-connected ⟨ S n ⟩ (de⊙ X)} {t₁ t₂ : has-level ⟨ S (S n) ⟩ (de⊙ X)} →
        –> (EM-Ω-==-from X t₁ c₁ ∘e EM-Ω-==-aux (X , t₁ , c₁) ∘e EM-Ω-==-to X t₁ c₁)
          ==
        –> (EM-Ω-==-from X t₂ c₂ ∘e EM-Ω-==-aux (X , t₂ , c₂) ∘e EM-Ω-==-to X t₂ c₂)
      to-invt = ap2 (λ t c → –> (EM-Ω-==-from X t c ∘e EM-Ω-==-aux (X , t , c) ∘e EM-Ω-==-to X t c)) (prop-has-all-paths _ _) (prop-has-all-paths _ _)

    from : (X == ⊙EM H (S (S n))) → (is-connected ⟨ S n ⟩ (de⊙ X) × Σ (has-level ⟨ S (S n) ⟩ (de⊙ X)) (λ tX → (Ω^'S-abgroup n X {{tX}} == H)))
    from p =
      let
        cX = transport (is-connected ⟨ S n ⟩) (! (ap de⊙ p)) (EM-conn H)
        tX =  transport (has-level ⟨ S (S n) ⟩) (! (ap de⊙ p)) (EM-level H _) in
      <– (EM-Ω-==-from X tX cX ∘e EM-Ω-==-aux (X , tX , cX) ∘e EM-Ω-==-to X tX cX) p

    abstract

      rt1 : (p : X == ⊙EM H (S (S n))) → to (from p) == p
      rt1 p =
        let
          cX = transport (is-connected ⟨ S n ⟩) (! (ap de⊙ p)) (EM-conn H)
          tX =  transport (has-level ⟨ S (S n) ⟩) (! (ap de⊙ p)) (EM-level H _) in
        <–-inv-r (EM-Ω-==-from X tX cX ∘e EM-Ω-==-aux (X , tX , cX) ∘e EM-Ω-==-to X tX cX) p

      rt2 : (t : is-connected ⟨ S n ⟩ (de⊙ X) × Σ (has-level ⟨ S (S n) ⟩ (de⊙ X)) (λ tX → (Ω^'S-abgroup n X {{tX}} == H))) → from (to t) == t
      rt2 t@(cX , tX , p) =
        ap (<– (EM-Ω-==-from X _ _ ∘e EM-Ω-==-aux (X , _ , _) ∘e EM-Ω-==-to X _ _)) (app= to-invt t) ∙
        <–-inv-l (EM-Ω-==-from X _ _ ∘e EM-Ω-==-aux (X , _ , _) ∘e EM-Ω-==-to X _ _) t

  abstract

    EM-Ω-==-ext : (X : Ptd i) →
      (is-connected ⟨ S n ⟩ (de⊙ X) × Σ (has-level ⟨ S (S n) ⟩ (de⊙ X)) (λ tX → (Ω^'S-abgroup n X {{tX}} == H)))
        ≃
      (⊙EM H (S (S n)) ⊙≃ X)
    EM-Ω-==-ext X = ⊙≃-ua ∘e !-equiv ∘e (EM-Ω-== X)
