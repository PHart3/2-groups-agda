{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.LoopSpace
open import lib.types.Paths
open import lib.types.Sigma

module lib.types.Homogeneous where

-- homogeneous types satisfying a coherence condition at the basepoint

module _ {i} {X : Type i} where

  module _ (x : X) where

    record homogeneous : Type i where
      constructor homog
      field
        auto : (y : X) → ⊙[ X , x ] ⊙≃ ⊙[ X , y ]
        homog-idf : fst (auto x) == ⊙idf ⊙[ X , x ]
    open homogeneous public

    homog-⊙Ω≃ : (y : X) → homogeneous → ⊙Ω ⊙[ X , x ] ⊙≃ ⊙Ω ⊙[ X , y ]
    homog-⊙Ω≃ y (homog auto _) = ⊙Ω-emap (auto y)

    homog-Ω≃ : (y : X) → homogeneous → (x == x) ≃ (y == y)
    homog-Ω≃ y η = ⊙≃-to-≃ (homog-⊙Ω≃ y η)

  {-
    Two pointed homotopies of pointed maps valued in a coherently homogeneous
    type are equal as soon as their underlying homotopies are equal.
  -}
  
  module _ {j} {Z : Type j} {z : Z} {f : Z → X} where

    ⊙∼-eval : ⊙[ f ∼ f , (λ z → idp) ] ⊙→ ⊙[ f z == f z , idp ]
    fst ⊙∼-eval = λ H → H z
    snd ⊙∼-eval = idp

    ⊙∼-eval-sect : homogeneous (f z) → has-sect⊙ ⊙∼-eval
    fst (has-sect⊙.r-inv (⊙∼-eval-sect η)) p = λ x₁ → –>(homog-Ω≃ (f z) (f x₁) η) p
    snd (has-sect⊙.r-inv (⊙∼-eval-sect (homog auto _))) =
      λ= λ x → Ω-fmap-β∙ (fst (auto (f x))) idp ∙
        !-inv-l (snd (fst (auto (f x))))
    has-sect⊙.sect⊙-eq (⊙∼-eval-sect (homog auto homog-idf)) =
      ⊙λ= (comp-to-⊙
        ((λ x → app= (ap (fst ∘ ⊙Ω-fmap) homog-idf ∙ ap fst ⊙Ω-fmap-idf) x) ,
        ↯ pathseq))
      where
        lemma : {m : ⊙[ X , f z ] ⊙→ ⊙[ X , f z ]} (τ : m == ⊙idf ⊙[ X , f z ]) 
          → ! (ap (λ u → u idp) (ap (fst ∘ ⊙Ω-fmap) τ) ∙ idp) ∙
            transport (λ v → Ω-fmap v idp == idp) (! τ) idp ∙ idp
            == idp
        lemma idp = idp

        pathseq :
          ! (ap (λ u → u idp)
            (ap (fst ∘ ⊙Ω-fmap) homog-idf ∙
            ap fst (pair= (λ= ap-idf)
              (↓-app=cst-in (ap (_∙ idp) (! (app=-β ap-idf idp))))))) ∙
          ap (λ H → H z) (λ= (λ x → Ω-fmap-β∙ (fst (auto (f x))) idp ∙
            !-inv-l (snd (fst (auto (f x)))))) ∙ idp
          =-=
          idp
        pathseq = 
          ! (ap (λ u → u idp)
            (ap (fst ∘ ⊙Ω-fmap) homog-idf ∙
            ap fst (pair= (λ= ap-idf) _))) ∙
          ap (λ H → H z) (λ= (λ x → Ω-fmap-β∙ (fst (auto (f x))) idp ∙
            !-inv-l (snd (fst (auto (f x)))))) ∙ idp
            =⟪ ap (λ p → ! p ∙ ap (λ H → H z)
                   (λ= (λ x → Ω-fmap-β∙ (fst (auto (f x))) idp ∙
                   !-inv-l (snd (fst (auto (f x)))))) ∙ idp) (
                 ap-∙ (λ u → u idp) (ap (fst ∘ ⊙Ω-fmap) homog-idf)
                   (ap fst (pair= (λ= ap-idf) _))) ⟫
          ! (ap (λ u → u idp) (ap (fst ∘ ⊙Ω-fmap) homog-idf) ∙
            ap (λ u → u idp) (ap fst (pair= (λ= ap-idf) _))) ∙
          ap (λ H → H z) (λ= (λ x → Ω-fmap-β∙ (fst (auto (f x))) idp ∙
            !-inv-l (snd (fst (auto (f x)))))) ∙ idp
            =⟪ ap (λ p → ! (ap (λ u → u idp) (ap (fst ∘ ⊙Ω-fmap)
                    homog-idf) ∙ p) ∙ ap (λ H → H z)
                    (λ= (λ x → Ω-fmap-β∙ (fst (auto (f x))) idp ∙
                    !-inv-l (snd (fst (auto (f x)))))) ∙ idp)
                  (ap (ap (λ u → u idp)) (fst=-β (λ= ap-idf)
                    (↓-app=cst-in (ap (_∙ idp) (! (app=-β ap-idf idp))))) ∙ λ=-ap-idf) ⟫
          ! (ap (λ u → u idp) (ap (fst ∘ ⊙Ω-fmap)
            homog-idf) ∙ idp) ∙
          ap (λ H → H z) (λ= (λ x → Ω-fmap-β∙ (fst (auto (f x))) idp ∙
            !-inv-l (snd (fst (auto (f x)))))) ∙ idp
          =⟪ ap (λ p → ! (ap (λ u → u idp) (ap (fst ∘ ⊙Ω-fmap)
               homog-idf) ∙ idp) ∙ p ∙ idp) (
               funext-nat-∼  z (λ x → Ω-fmap-β∙ (fst (auto (f x))) idp ∙
               !-inv-l (snd (fst (auto (f x)))))) ⟫
          ! (ap (λ u → u idp) (ap (fst ∘ ⊙Ω-fmap)
            homog-idf) ∙ idp) ∙
          (Ω-fmap-β∙ (fst (auto (f z))) idp ∙
            !-inv-l (snd (fst (auto (f z))))) ∙ idp
            =⟪ ap (λ p → ! (ap (λ u → u idp) (ap (fst ∘ ⊙Ω-fmap)
               homog-idf) ∙ idp) ∙ p ∙ idp)
               (! (apd-tr (λ F → Ω-fmap-β∙ F idp ∙ !-inv-l (snd F))
               (! homog-idf))) ⟫
          ! (ap (λ u → u idp) (ap (fst ∘ ⊙Ω-fmap)
            homog-idf) ∙ idp) ∙
          transport (λ v → Ω-fmap v idp == idp)
            (! homog-idf) idp ∙ idp
            =⟪ lemma homog-idf ⟫
          idp ∎∎

    ⊙∼-evalΩ-sect : homogeneous (f z) → has-sect⊙ (⊙Ω-fmap ⊙∼-eval)
    ⊙∼-evalΩ-sect η = ⊙Ω-sect (⊙∼-eval) (⊙∼-eval-sect η)

    module _ (η : homogeneous (f z)) where

      open has-sect⊙

      ∼⊙homog= : (x : X) {g : Z → X}
        {fₚ : f z == x} {gₚ : g z == x}
        {H₁ H₂ : f == g}
        {H₁ₚ : ! (app= H₁ z) ∙ fₚ == gₚ}
        {H₂ₚ : ! (app= H₂ z) ∙ fₚ == gₚ}
        →  H₁ == H₂ → (app= H₁ , H₁ₚ) ⊙→∼ (app= H₂ , H₂ₚ)
      fst (∼⊙homog= x {fₚ = idp} {H₁ = idp} {H₁ₚ = H₁ₚ} {H₂ₚ} idp) =
        λ x₁ → app= (fst (r-inv (⊙∼-evalΩ-sect η))
          (ap-post∙idp∘!-inv (H₁ₚ ∙ ! (H₂ₚ)))) x₁
      snd (∼⊙homog= x {fₚ = idp} {H₁ = idp} {H₁ₚ = H₁ₚ} {H₂ₚ} idp) =
        post↯-rotate-in (=ₛ-in (ap (ap (λ p → ! p ∙ idp))
        (app= (ap fst (sect⊙-eq (⊙∼-evalΩ-sect η)))
          (ap-post∙idp∘!-inv (H₁ₚ ∙ ! (H₂ₚ)))) ∙
        <–-inv-r (ap-equiv (post∙idp∘!-is-equiv) idp idp)
          (H₁ₚ ∙ ! (H₂ₚ))))

      ∼⊙homog∼ : (x : X) {g : Z → X}
        {fₚ : f z == x} {gₚ : g z == x}
        {H₁ H₂ : f ∼ g}
        {H₁ₚ : ! (H₁ z) ∙ fₚ == gₚ}
        {H₂ₚ : ! (H₂ z) ∙ fₚ == gₚ}
        →  H₁ ∼ H₂ → (H₁ , H₁ₚ) ⊙→∼ (H₂ , H₂ₚ)
      fst (∼⊙homog∼ x {fₚ = idp} {gₚ} {H₁} {H₂} {H₁ₚ} {H₂ₚ} K) t =
        ! (app=-β H₁ t) ∙
        fst (∼⊙homog= x {fₚ = idp} {gₚ = gₚ} {H₁ = λ= H₁} {H₂ = λ= H₂}
          {H₁ₚ = (ap (λ p → ! p ∙ idp) (app=-β H₁ z) ∙ H₁ₚ)}
          {H₂ₚ = (ap (λ p → ! p ∙ idp) (app=-β H₂ z) ∙ H₂ₚ)}
          (ap λ= (λ= K))) t ∙
        app=-β H₂ t
      snd (∼⊙homog∼ x {fₚ = idp} {gₚ} {H₁} {H₂} {H₁ₚ} {H₂ₚ} K) =
        ap (λ p → ! p ∙ idp) (! (app=-β H₁ z) ∙
          fst (∼⊙homog= (f z) {fₚ = idp} {gₚ = gₚ} {H₁ = λ= H₁} {H₂ = λ= H₂}
            {H₁ₚ = (ap (λ p → ! p ∙ idp) (app=-β H₁ z) ∙ H₁ₚ)}
            {H₂ₚ = (ap (λ p → ! p ∙ idp) (app=-β H₂ z) ∙ H₂ₚ)}
            (ap λ= (λ= K))) z ∙ app=-β H₂ z) ◃∙
        H₂ₚ ◃∎
          =ₛ₁⟨ 0 & 1 & ap-!∙∙ (λ p → ! p ∙ idp) (app=-β H₁ z)
               (fst (∼⊙homog= (f z) {fₚ = idp} {gₚ = gₚ} {H₁ = λ= H₁} {H₂ = λ= H₂}
                 {H₁ₚ = (ap (λ p → ! p ∙ idp) (app=-β H₁ z) ∙ H₁ₚ)}
                 {H₂ₚ = (ap (λ p → ! p ∙ idp) (app=-β H₂ z) ∙ H₂ₚ)}
                 (ap λ= (λ= K))) z) (app=-β H₂ z) ⟩
        ↯ (! (ap (λ p → ! p ∙ idp) (app=-β H₁ z)) ◃∙
         ap (λ p → ! p ∙ idp) (fst (∼⊙homog= (f z) {fₚ = idp} {gₚ = gₚ}
              {H₁ = λ= H₁} {H₂ = λ= H₂}
              {H₁ₚ = (ap (λ p → ! p ∙ idp) (app=-β H₁ z) ∙ H₁ₚ)}
              {H₂ₚ = (ap (λ p → ! p ∙ idp) (app=-β H₂ z) ∙ H₂ₚ)}
              (ap λ= (λ= K))) z) ◃∙
         ap (λ p → ! p ∙ idp) (app=-β H₂ z) ◃∎) ◃∙ H₂ₚ ◃∎
           =ₛ⟨ pre-rotate-in-↯-assoc
                 (snd (∼⊙homog= x
                 {fₚ = idp} {gₚ = gₚ} {H₁ = λ= H₁} {H₂ = λ= H₂}
                 {H₁ₚ = (ap (λ p → ! p ∙ idp) (app=-β H₁ z) ∙ H₁ₚ)}
                 {H₂ₚ = (ap (λ p → ! p ∙ idp) (app=-β H₂ z) ∙ H₂ₚ)}
                 (ap λ= (λ= K)))) ⟩
         H₁ₚ ◃∎ ∎ₛ

-- All loop spaces are coherently homogeneous.

module _ {i} {X : Type i} {x : X} where

  module _ {p : x == x} where

    loop-homog : homogeneous p
    fst (fst (auto loop-homog q)) = λ ℓ → ℓ ∙ ! p ∙ q
    snd (fst (auto loop-homog q)) =
      ! (∙-assoc p (! p) q) ∙ ap (λ c → c ∙ q) (!-inv-r p)
    snd (auto loop-homog q) = post∙-is-equiv (! p ∙ q)
    homog-idf loop-homog =
      ⊙λ= (comp-to-⊙ ((λ x₁ → ap (λ c → x₁ ∙ c) (!-inv-l p) ∙ ∙-unit-r x₁) ,
        !-inv-l-r-unit-assoc p))

  ∼⊙Ωhomog∼ : ∀ {j} {Z : Ptd j} {p : x == x}
    {f g : Z ⊙→ ⊙[ x == x , p ]}
    {H₁ H₂ : fst f ∼ fst g}
    {H₁ₚ : ! (H₁ (pt Z)) ∙ snd f == snd g}
    {H₂ₚ : ! (H₂ (pt Z)) ∙ snd f == snd g}
    →  H₁ ∼ H₂ → (H₁ , H₁ₚ) ⊙→∼ (H₂ , H₂ₚ)
  ∼⊙Ωhomog∼ {Z = Z} {p} {f} K = ∼⊙homog∼ (loop-homog {p = fst f (pt Z)}) p K

