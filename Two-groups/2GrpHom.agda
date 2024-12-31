{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp

module 2GrpHom where

open CohGrp {{...}}

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  (map : G₁ → G₂) (map-comp : (x y : G₁) → mu (map x) (map y) == map (mu x y))
  (map-id : id == map id)where

  module _ (map-inv : (x : G₁) → inv (map x) == map (inv x))
    (map-lam : (x : G₁) →
      ! (lam (map x)) ◃∎
      =ₛ
      ! (ap map (lam x)) ◃∙ ! (map-comp id x) ◃∙ ! (ap (λ z → mu z (map x)) map-id) ◃∎) where

    linv-to-rinv : (x : G₁) →
      ap (mu (map x)) (map-inv x)
      ==
      ! (rinv (map x)) ∙
      map-id ∙
      ap map (rinv x) ∙
      ! (map-comp x (inv x))
      → 
      ! (! (al (inv (map x)) (map x) (inv (map x))) ∙
        ! (ap (mu (inv (map x))) (rinv (map x))) ∙ rho (inv (map x))) ◃∙
      ap (λ z → mu z (inv (map x)))
        (linv (map x) ∙ map-id ∙ ! (ap map (linv x)) ∙ ! (map-comp (inv x) x)) ◃∙
      ! (al (map (inv x)) (map x) (inv (map x))) ◃∙
      ! (ap (mu (map (inv x))) (rinv (map x))) ◃∙
      rho (map (inv x)) ◃∎
      =ₛ
      map-inv x ◃∎
    linv-to-rinv x ρ = 
      _
        =ₛ⟨ 0 & 1 &
          !-!∙!∙ (al (inv (map x)) (map x) (inv (map x)))
            (ap (mu (inv (map x))) (rinv (map x))) _ ⟩
      _
        =ₛ⟨ 3 & 1 &
          ap-∙∙!! (λ z → mu z (inv (map x))) (linv (map x)) (map-id) (ap map (linv x)) _ ⟩
      ! (rho (inv (map x))) ◃∙
      ap (mu (inv (map x))) (rinv (map x)) ◃∙
      al (inv (map x)) (map x) (inv (map x)) ◃∙
      ap (λ z → mu z (inv (map x))) (linv (map x)) ◃∙
      ap (λ z → mu z (inv (map x))) map-id ◃∙
      ! (ap (λ z → mu z (inv (map x))) (ap map (linv x))) ◃∙
      ! (ap (λ z → mu z (inv (map x))) (map-comp (inv x) x)) ◃∙
      ! (al (map (inv x)) (map x) (inv (map x))) ◃∙
      ! (ap (mu (map (inv x))) (rinv (map x))) ◃∙
      rho (map (inv x)) ◃∎
        =ₛ₁⟨ 0 & 4 & ! (zz₂ (map x)) ⟩
      _
        =ₛ⟨ 0 & 1 & hmtpy-nat-!◃ lam (map-inv x) ⟩
      _
        =ₛ⟨ 1 & 1 & map-lam (inv x)  ⟩
      _
        =ₛ⟨ 2 & 1 & hmtpy-nat-!◃-! (λ z → map-comp z (inv x)) (linv x) ⟩
      _
        =ₛ⟨ 4 & 1 & apCommSq◃ (λ z → ap (mu (map z)) (map-inv x)) (linv x) ⟩
      {!!}

{-

ap (mu (map x)) ()
==
! (rinv (map x)) ∙ map-id ∙ ap map (rinv x) ∙ ! (map-comp x (inv x))

-}

{-
  rho-to-lam : (x : G₁)
    → ap (λ z → mu z (map x)) (mu-ff<– (map x) _ _ (rho (map x) ∙ ! (ap map (rho x)) ∙ ! (map-comp x id))) ∙
      map-comp id x ∙ ap map (lam x)
      ==
      lam (map x)
  rho-to-lam x = 
    ap (λ z → mu z (map x)) (mu-ff<– (map x) _ _ (rho (map x) ∙ ! (ap map (rho x)) ∙ ! (map-comp x id))) ∙
      map-comp id x ∙ ap map (lam x)
      =⟨ ap (λ p → ap (λ z → mu z (map x))
              (mu-ff<– (map x) _ _ (rho (map x) ∙ ! (ap map (rho x)) ∙ ! (map-comp x id))) ∙
            map-comp id x ∙ ap map p) (zz₁ x) ⟩
    {!!}
      =⟨ {!!} ⟩
    ap (λ z → mu z (map x)) (rinv (map x)) ∙
    ! (al (map x) (inv (map x)) (map x)) ∙
    ap (mu (map x)) (linv (map x)) ∙ rho (map x)
      =⟨ ! (zz₁ (map x)) ⟩
    lam (map x) =∎
    where
      lemma1 :
        ap (λ z → mu z (map x)) (! (al (inv (map x)) (map x) id ∙ ap2 mu (linv (map x)) idp ∙ lam id))
          ==
        {!!}
      lemma1 = 
        ap (λ z → mu z (map x)) (! (al (inv (map x)) (map x) id ∙ ap2 mu (linv (map x)) idp ∙ lam id))
          =⟨ ap-! (λ z → mu z (map x)) _  ⟩
        _
          =⟨ ap ! (ap-∙∙ (λ z → mu z (map x)) (al (inv (map x)) (map x) id) (ap2 mu (linv (map x)) idp) _)  ⟩
        ! (ap (λ z → mu z (map x)) (al (inv (map x)) (map x) id) ∙
        ap (λ z → mu z (map x)) (ap2 mu (linv (map x)) idp) ∙
        ap (λ z → mu z (map x)) (lam id))
          =⟨ ap ! (ap3 (λ p₁ p₂ p₃ →  p₁ ∙ p₂ ∙ p₃)
               (idp {a = ap (λ z → mu z (map x)) (al (inv (map x)) (map x) id)})
               (ap (ap (λ z → mu z (map x))) (ap2-idp-r mu (linv (map x))) ∙ 
                 ∘-ap (λ z → mu z (map x)) (λ z → mu z id) (linv (map x)) ∙
                 hmpty-nat-∙'-r (λ z → ! (al z id (map x)) ∙ ap (mu z) (lam (map x))) (linv (map x)))
               (idp {a = ap (λ z → mu z (map x)) (lam id)}))  ⟩
        {!_
          =⟨  ⟩
        ?!}
-}
  -- equivalence between the two definitions of 2-group morphism

{-

ap (λ z → mu z (map x))
(!
 (al (inv (map x)) (map x) id ∙
  ap2 mu (linv (map x)) idp ∙
  lam id)
 ∙
 ap (mu (inv (map x)))
 (rho (map x) ∙
  ! (ap map (rho x)) ∙ ! (map-comp x id))
 ∙
 al (inv (map x)) (map x) (map id) ∙
 ap2 mu (linv (map x)) idp ∙
 lam (map id))
∙ map-comp id x ∙ ap map (lam x)
== lam (map x)

-}
