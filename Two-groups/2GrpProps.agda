{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp

module 2GrpProps where

open CohGrp {{...}}

-- properties of all monoidal cats
module _ {i} {G : Type i} {{η : CohGrp G}} where

  abstract

    pent-rot : (w x y z : G) →
      al w x (mu y z) ◃∙ al (mu w x) y z ◃∙ ! (ap (λ v → mu v z) (al w x y)) ◃∎
        =ₛ
      ap (mu w) (al x y z) ◃∙ al w (mu x y) z ◃∎
    pent-rot w x y z =
      post-rotate'-seq-in
        {r = al w x (mu y z) ◃∙ al (mu w x) y z ◃∎}
        {q = ap (λ v → mu v z) (al w x y) ◃∎}
        (=ₛ-in (pent w x y z))

    rho-lam-id-eq : rho id ◃∎ =ₛ lam id ◃∎
    rho-lam-id-eq =
      {!!}

  module _ (x y : G) where

    private
    
      lam-alid-lam0 = 
        ap (mu id) (ap (λ v → mu v y) (! (lam x))) ◃∙
        ap (mu id) (! (al id x y)) ◃∙
        ap (mu id) (lam (mu x y)) ◃∎
          =ₛ₁⟨ 0 & 1 &
            ∘-ap (mu id) (λ z → mu z y) (! (lam x))
            ∙ ap-! (λ z → mu id (mu z y)) (lam x) ⟩
        _
          =ₛ⟨ 0 & 1 & hmpty-nat-∙◃! (λ z → al id z y) (lam x) ⟩
        _
          =ₛ⟨ 0 & 1 & apCommSq2◃ (λ z → al z x y) (rho id) ⟩
        _
          =ₛ₁⟨ 2 & 1 & ap-∘ (λ z → mu z y) (λ z → mu z x) (rho id) ⟩
        ! (ap (λ z → mu z (mu x y)) (rho id)) ◃∙
        al (mu id id) x y ◃∙
        ap (λ z → mu z y) (ap (λ z → mu z x) (rho id)) ◃∙
        ! (ap (λ z → mu (mu id z) y) (lam x)) ◃∙
        ! (al id (mu id x) y) ◃∙
        ap (mu id) (! (al id x y)) ◃∙
        ap (mu id) (lam (mu x y)) ◃∎ ∎ₛ

      lam-alid-lam1 = 
        ! (ap (λ z → mu z (mu x y)) (rho id)) ◃∙
        al (mu id id) x y ◃∙
        ap (λ z → mu z y) (ap (λ z → mu z x) (rho id)) ◃∙
        ! (ap (λ z → mu (mu id z) y) (lam x)) ◃∙
        ! (al id (mu id x) y) ◃∙
        ap (mu id) (! (al id x y)) ◃∙
        ap (mu id) (lam (mu x y)) ◃∎
          =ₛ₁⟨ 2 & 1 & ap (ap (λ z → mu z y)) (tr id x) ⟩
        _
          =ₛ₁⟨ 0 & 1 & ap ! (tr id (mu x y)) ⟩
        ! (! (al id id (mu x y)) ∙
          ap (mu id) (lam (mu x y))) ◃∙
        al (mu id id) x y ◃∙
        ap (λ z → mu z y)
          (! (al id id x) ∙ ap (mu id) (lam x)) ◃∙
        ! (ap (λ z → mu (mu id z) y) (lam x)) ◃∙
        ! (al id (mu id x) y) ◃∙
        ap (mu id) (! (al id x y)) ◃∙
        ap (mu id) (lam (mu x y)) ◃∎
          =ₛ⟨ 0 & 1 & !-!-∙ (al id id (mu x y)) _  ⟩
        _
          =ₛ⟨ 3 & 1 & ap-!-∙-∘ (λ z → mu z y) (mu id) (lam x) (al id id x) ⟩
        ! (ap (mu id) (lam (mu x y))) ◃∙
        al id id (mu x y) ◃∙
        al (mu id id) x y ◃∙
        ! (ap (λ z → mu z y) (al id id x)) ◃∙
        ap ((λ z → mu z y) ∘ mu id) (lam x) ◃∙
        ! (ap (λ z → mu (mu id z) y) (lam x)) ◃∙
        ! (al id (mu id x) y) ◃∙
        ap (mu id) (! (al id x y)) ◃∙
        ap (mu id) (lam (mu x y)) ◃∎ ∎ₛ

      lam-alid-lam2 =
        ! (ap (mu id) (lam (mu x y))) ◃∙
        al id id (mu x y) ◃∙
        al (mu id id) x y ◃∙
        ! (ap (λ z → mu z y) (al id id x)) ◃∙
        ap ((λ z → mu z y) ∘ mu id) (lam x) ◃∙
        ! (ap (λ z → mu (mu id z) y) (lam x)) ◃∙
        ! (al id (mu id x) y) ◃∙
        ap (mu id) (! (al id x y)) ◃∙
        ap (mu id) (lam (mu x y)) ◃∎
          =ₛ⟨ 1 & 3 & pent-rot id id x y ⟩
        _
          =ₛ₁⟨ 3 & 2 & !-inv-r (ap (λ z → mu (mu id z) y) (lam x)) ⟩
        _
          =ₛ₁⟨ 2 & 3 & !-inv-r (al id (mu id x) y) ⟩
        ! (ap (mu id) (lam (mu x y))) ◃∙
        ap (mu id) (al id x y) ◃∙
        idp ◃∙
        ap (mu id) (! (al id x y)) ◃∙
        ap (mu id) (lam (mu x y)) ◃∎ ∎ₛ

      lam-alid-lam3 =
        ! (ap (mu id) (lam (mu x y))) ◃∙
        ap (mu id) (al id x y) ◃∙
        idp ◃∙
        ap (mu id) (! (al id x y)) ◃∙
        ap (mu id) (lam (mu x y)) ◃∎
          =ₛ₁⟨ 1 & 3 & ap-!-inv (mu id) (al id x y) ⟩
        _
          =ₛ₁⟨ !-inv-l (ap (mu id) (lam (mu x y)))  ⟩
        idp ◃∎ ∎ₛ

    abstract
      lam-alid-lam4 :
        ap (mu id) (
          ap (λ v → mu v y) (! (lam x)) ∙
          ! (al id x y) ∙
          lam (mu x y)) ◃∎
          =ₛ
        idp ◃∎
      lam-alid-lam4 =
        ap-seq-∙ (mu id) _ ∙ₛ
        (lam-alid-lam0 ∙ₛ (lam-alid-lam1 ∙ₛ (lam-alid-lam2 ∙ₛ lam-alid-lam3)))

    abstract
      lam-alid-lam :
        ap (λ v → mu v y) (! (lam x)) ∙
        ! (al id x y) ∙
        lam (mu x y)
          ==
        idp
      lam-alid-lam = ap-equiv-idp muid-iso (=ₛ-out lam-alid-lam4)

-- properties specific to 2-groups
module _ {i} {G : Type i} {{η : CohGrp G}} (x : G) where

  private

    abstract

      zz₁-rot◃ :
        ! (rho x) ◃∙
        ! (ap (mu x) (linv x)) ◃∙
        al x (inv x) x ◃∎
          =ₛ
        ! (lam x) ◃∙
        ap (λ z → mu z x) (rinv x) ◃∎
      zz₁-rot◃ =
        ! (rho x) ◃∙
        ! (ap (mu x) (linv x)) ◃∙
        al x (inv x) x ◃∎
          =ₛ₁⟨ 2 & 1 & ! (!-! (al x (inv x) x)) ⟩
        _
          =ₛ⟨ pre-rotate-in
                {p = lam x}
                (post-rotate'-seq-in
                  {r = lam x ◃∎}
                  {q =
                    ! (al x (inv x) x) ◃∙
                    ap (mu x) (linv x) ◃∙
                    rho x ◃∎}
                  {p = ap (λ z → mu z x) (rinv x) ◃∎}
                  (=ₛ-in (zz₁ x))) ⟩
        ! (lam x) ◃∙
        ap (λ z → mu z x) (rinv x) ◃∎ ∎ₛ

      zz₂-rot◃ :
        rho (inv x) ◃∎
          =ₛ
        ap (mu (inv x)) (rinv x) ◃∙
        al (inv x) x (inv x) ◃∙
        ap (λ z → mu z (inv x)) (linv x) ◃∙
        lam (inv x) ◃∎
      zz₂-rot◃ = 
        rho (inv x) ◃∎
          =ₛ₁⟨ ! (!-! (rho (inv x))) ⟩
        _
          =ₛ⟨ post-rotate-in
                {r =
                  ap (mu (inv x)) (rinv x) ◃∙
                  al (inv x) x (inv x) ◃∙
                  ap (λ z → mu z (inv x)) (linv x) ◃∎}
                {q = ! (lam (inv x))}
                (pre-rotate'-in
                  {p = ! (rho (inv x))}
                  (=ₛ-in (zz₂ x)))  ⟩
        ap (mu (inv x)) (rinv x) ◃∙
        al (inv x) x (inv x) ◃∙
        ap (λ z → mu z (inv x)) (linv x) ◃∙
        ! (! (lam (inv x))) ◃∎
          =ₛ₁⟨ 3 & 1 & !-! (lam (inv x)) ⟩
        ap (mu (inv x)) (rinv x) ◃∙
        al (inv x) x (inv x) ◃∙
        ap (λ z → mu z (inv x)) (linv x) ◃∙
        lam (inv x) ◃∎ ∎ₛ

    abstract
      zz₁-rinv-aux :
        rinv x ◃∎
          =ₛ
        ! (! (al id x (inv x)) ∙ ! (ap (mu id) (rinv x)) ∙ rho id) ◃∙
        ap (λ z → mu z (inv x))
          (lam x ∙ ! (rho x) ∙ ! (ap (mu x) (linv x)) ∙ al x (inv x) x) ◃∙
        ! (al (mu x (inv x)) x (inv x)) ◃∙
        ! (ap (mu (mu x (inv x))) (rinv x)) ◃∙
        rho (mu x (inv x)) ◃∎
      zz₁-rinv-aux = =ₛ-in (
        ! (<–-inv-l (ap-equiv ((λ z → mu z x) , mu-post-iso x) _ _) (rinv x)) ∙
        ap (mu-post-ff<– x id (mu x (inv x)))
          (tri-rot (ap (λ z → mu z x) (rinv x)) _ (ap (mu x) (linv x)) (rho x) (zz₁ x)))
  {-
    zz₁-rinv-suff :
      ap (λ z → mu z (inv x))
        (! (rho x) ∙ ! (ap (mu x) (linv x)) ∙ al x (inv x) x) ◃∙
      (! (al (mu x (inv x)) x (inv x)) ∙
      ! (ap (mu (mu x (inv x))) (rinv x)) ∙
      rho (mu x (inv x))) ◃∎
        =ₛ
      idp ◃∎
    zz₁-rinv-suff = 
      ap (λ z → mu z (inv x))
        (! (rho x) ∙ ! (ap (mu x) (linv x)) ∙ al x (inv x) x) ◃∙
      (! (al (mu x (inv x)) x (inv x)) ∙
      ! (ap (mu (mu x (inv x))) (rinv x)) ∙
      rho (mu x (inv x))) ◃∎
        =ₛ₁⟨ 0 & 1 & ap (ap (λ z → mu z (inv x))) (=ₛ-out (zz₁-rot◃)) ⟩
      _
        =ₛ⟨ 1 & 1 & 
          apCommSq2◃
            (λ z → ! (al z x (inv x)) ∙ ! (ap (mu z) (rinv x)) ∙ rho z)
            (rinv x) ⟩
      _
        =ₛ⟨ 2 & 1 & =ₛ-in idp ⟩
      ap (λ z → mu z (inv x))
        (! (lam x) ∙ ap (λ z → mu z x) (rinv x)) ◃∙
      ! (ap (λ z → mu (mu z x) (inv x)) (rinv x)) ◃∙
      ! (al id x (inv x)) ◃∙
      ! (ap (mu id) (rinv x)) ◃∙
      rho id ◃∙
      ap (λ z → z) (rinv x) ◃∎
        =ₛ⟨ 3 & 1 & hmpty-nat-∙◃! lam (rinv x) ⟩
      ap (λ z → mu z (inv x))
        (! (lam x) ∙ ap (λ z → mu z x) (rinv x)) ◃∙
      ! (ap (λ z → mu (mu z x) (inv x)) (rinv x)) ◃∙
      ! (al id x (inv x)) ◃∙
      lam (mu x (inv x)) ◃∙
      ! (ap (λ z → z) (rinv x)) ◃∙
      ! (lam id) ◃∙
      rho id ◃∙
      ap (λ z → z) (rinv x) ◃∎
        =ₛ⟨ 6 & 1 & rho-lam-id-eq ⟩
      _
        =ₛ₁⟨ 5 & 2 & !-inv-l (lam id) ⟩
      _
        =ₛ₁⟨ 4 & 3 & !-inv-l (ap (λ z → z) (rinv x)) ⟩
      _
        =ₛ⟨ 0 & 1 & =ₛ-in
          (ap-∙ (λ z → mu z (inv x)) (! (lam x)) (ap (λ z → mu z x) (rinv x))) ⟩
      ap (λ z → mu z (inv x)) (! (lam x)) ◃∙
      ap (λ z → mu z (inv x)) (ap (λ z → mu z x) (rinv x)) ◃∙
      ! (ap (λ z → mu (mu z x) (inv x)) (rinv x)) ◃∙
      ! (al id x (inv x)) ◃∙
      lam (mu x (inv x)) ◃∙
      idp ◃∎
        =ₛ₁⟨ 1 & 2 & ap-∘-!-inv-r (λ z → mu z (inv x)) (λ z → mu z x) (rinv x) ⟩
      _
        =ₛ⟨ 0 & 4 & =ₛ-in ? ⟩
      idp ◃∙ idp ◃∎
        =ₛ₁⟨ idp ⟩
      idp ◃∎ ∎ₛ

  abstract
    zz₁-rinv = 
  -}
