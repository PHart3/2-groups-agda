{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp
open import 2GrpProps

module 2GrpProps2 where

open CohGrp {{...}}

module _ {i} {G : Type i} {{η : CohGrp G}} where

  module _ (y x : G) where
      
    rho-alid-rho0 =
      ap (λ z → mu z id) (! (rho (mu y x))) ◃∙
      ap (λ z → mu z id) (! (al y x id)) ◃∙
      ap (λ z → mu z id) (ap (mu y) (rho x)) ◃∎
        =ₛ⟨ 0 & 2 & !-!-ap-∙◃ (λ z → mu z id) (rho (mu y x)) (al y x id) ⟩
      ! (ap (λ z → mu z id) (rho (mu y x))) ◃∙
      ! (ap (λ z → mu z id) (al y x id)) ◃∙
      ap (λ z → mu z id) (ap (mu y) (rho x)) ◃∎
        =ₛ₁⟨ 2 & 1 & ∘-ap (λ z → mu z id) (mu y) (rho x) ⟩
      ! (ap (λ z → mu z id) (rho (mu y x))) ◃∙
      ! (ap (λ z → mu z id) (al y x id)) ◃∙
      ap (λ z → mu (mu y z) id) (rho x) ◃∎
        =ₛ⟨ 2 & 1 & apCommSq◃ (λ z → al y z id) (rho x) ⟩
      ! (ap (λ z → mu z id) (rho (mu y x))) ◃∙
      ! (ap (λ z → mu z id) (al y x id)) ◃∙
      ! (al y (mu x id) id) ◃∙
      ap (λ z → mu y (mu z id)) (rho x) ◃∙
      al y x id ◃∎
        =ₛ₁⟨ 3 & 1 & ap-∘ (mu y) (λ z → mu z id) (rho x) ⟩
      _
        =ₑ⟨ 3 & 1 & (ap (mu y) (! (al x id id)) ◃∙ ap (mu y) (ap (mu x) (lam id)) ◃∎)
          % ap-seq-=ₛ (mu y) (=ₛ-in (tr x id)) ⟩
      ! (ap (λ z → mu z id) (rho (mu y x))) ◃∙
      ! (ap (λ z → mu z id) (al y x id)) ◃∙
      ! (al y (mu x id) id) ◃∙
      ap (mu y) (! (al x id id)) ◃∙
      ap (mu y) (ap (mu x) (lam id)) ◃∙
      al y x id ◃∎
        =ₛ₁⟨ 4 & 1 & ∘-ap (mu y) (mu x) (lam id) ⟩
      _
        =ₛ⟨ 4 & 1 & hmtpy-nat-∙◃ (al y x) (lam id) ⟩
      ! (ap (λ z → mu z id) (rho (mu y x))) ◃∙
      ! (ap (λ z → mu z id) (al y x id)) ◃∙
      ! (al y (mu x id) id) ◃∙
      ap (mu y) (! (al x id id)) ◃∙
      al y x (mu id id) ◃∙
      ap (mu (mu y x)) (lam id) ◃∙
      ! (al y x id) ◃∙
      al y x id ◃∎
        =ₛ⟨ 5 & 1 & !ₛ (tr-rot (mu y x) id) ⟩
      ! (ap (λ z → mu z id) (rho (mu y x))) ◃∙
      ! (ap (λ z → mu z id) (al y x id)) ◃∙
      ! (al y (mu x id) id) ◃∙
      ap (mu y) (! (al x id id)) ◃∙
      al y x (mu id id) ◃∙
      al (mu y x) id id ◃∙
      ap (λ z → mu z id) (rho (mu y x)) ◃∙
      ! (al y x id) ◃∙
      al y x id ◃∎ ∎ₛ

    rho-alid-rho1 =
      ! (ap (λ z → mu z id) (rho (mu y x))) ◃∙
      ! (ap (λ z → mu z id) (al y x id)) ◃∙
      ! (al y (mu x id) id) ◃∙
      ap (mu y) (! (al x id id)) ◃∙
      al y x (mu id id) ◃∙
      al (mu y x) id id ◃∙
      ap (λ z → mu z id) (rho (mu y x)) ◃∙
      ! (al y x id) ◃∙
      al y x id ◃∎
        =ₛ₁⟨ 3 & 1 & ap-! (mu y) (al x id id) ⟩
      _
        =ₑ⟨ 4 & 2 & (ap (mu y) (al x id id) ◃∙ al y (mu x id) id ◃∙ ap (λ v → mu v id) (al y x id) ◃∎)
          % =ₛ-in (pent y x id id) ⟩
      ! (ap (λ z → mu z id) (rho (mu y x))) ◃∙
      ! (ap (λ z → mu z id) (al y x id)) ◃∙
      ! (al y (mu x id) id) ◃∙
      ! (ap (mu y) (al x id id)) ◃∙
      ap (mu y) (al x id id) ◃∙
      al y (mu x id) id ◃∙
      ap (λ v → mu v id) (al y x id) ◃∙
      ap (λ z → mu z id) (rho (mu y x)) ◃∙
      ! (al y x id) ◃∙
      al y x id ◃∎
        =ₛ₁⟨ 3 & 2 & !-inv-l (ap (mu y) (al x id id)) ⟩
      _
        =ₛ₁⟨ 2 & 3 & !-inv-l (al y (mu x id) id) ⟩
      _
        =ₛ₁⟨ 1 & 3 & !-inv-l (ap (λ z → mu z id) (al y x id)) ⟩
      _
        =ₛ₁⟨ 0 & 3 & !-inv-l (ap (λ z → mu z id) (rho (mu y x))) ⟩
      _
        =ₛ₁⟨ !-inv-l (al y x id) ⟩
      idp ◃∎ ∎ₛ

    abstract
      rho-alid-rho2 :
        ap (λ z → mu z id) (
          ! (rho (mu y x)) ∙
          ! (al y x id) ∙
          ap (mu y) (rho x)) ◃∎
          =ₛ
        idp ◃∎
      rho-alid-rho2 = ap-seq-∙ (λ z → mu z id) _ ∙ₛ rho-alid-rho0 ∙ₛ rho-alid-rho1

    abstract
      rho-alid-rho :
        ! (rho (mu y x)) ◃∙
        ! (al y x id) ◃∙
        ap (mu y) (rho x) ◃∎
          =ₛ
        idp ◃∎
      rho-alid-rho = =ₛ-in (ap-equiv-idp idmu-iso (=ₛ-out rho-alid-rho2))


  module _ (x : G) where

    abstract
      zz₁-rot2◃ :
        al x (inv x) x ◃∙
        ! (ap (λ z → mu z x) (rinv x)) ◃∙
        lam x ◃∎
          =ₛ
        ap (mu x) (linv x) ◃∙
        rho x ◃∎
      zz₁-rot2◃ = pre-rotate-out (pre-rotate'-in (=ₛ-in (zz₁ x)))

    abstract

      zz₁-linv-aux :
        linv x ◃∎
          =ₛ
        ! (al (inv x) x (mu (inv x) x) ∙
          ap2 mu (linv x) idp ∙
          lam (mu (inv x) x)) ◃∙
        ap (mu (inv x))
          (al x (inv x) x ∙
          ! (ap (λ z → mu z x) (rinv x)) ∙
          lam x ∙
          ! (rho x)) ◃∙
        al (inv x) x id ◃∙
        ap2 mu (linv x) idp ◃∙
        lam id ◃∎
      zz₁-linv-aux =
        linv x ◃∎
          =ₛ⟨ =ₛ-in (
              ! (<–-inv-l (ap-equiv (mu x , mu-pre-iso x) _ _) (linv x)) ∙
                ap (mu-pre-ff<– x (mu (inv x) x) id)
                  (tri-rot2 (ap (λ z → mu z x) (rinv x)) (al x (inv x) x) (ap (mu x) (linv x)) (rho x) (zz₁ x))) ⟩
        ! (al (inv x) x (mu (inv x) x) ∙
          ap2 mu (linv x) idp ∙
          lam (mu (inv x) x)) ◃∙
        ap (mu (inv x))
          (al x (inv x) x ∙
          ! (ap (λ z → mu z x) (rinv x)) ∙
          lam x ∙
          ! (rho x)) ◃∙
        al (inv x) x id ◃∙
        ap2 mu (linv x) idp ◃∙
        lam id ◃∎ ∎ₛ

      zz₁-linv-suff :
        ! (al (inv x) x (mu (inv x) x) ∙
          ap2 mu (linv x) idp ∙
          lam (mu (inv x) x)) ◃∙
        ap (mu (inv x)) (al x (inv x) x) ◃∙
        ap (mu (inv x)) (! (ap (λ z → mu z x) (rinv x))) ◃∙
        ap (mu (inv x)) (lam x) ◃∎
          =ₛ
        idp ◃∎
      zz₁-linv-suff = 
        ! (al (inv x) x (mu (inv x) x) ∙
          ap2 mu (linv x) idp ∙
          lam (mu (inv x) x)) ◃∙
        ap (mu (inv x)) (al x (inv x) x) ◃∙
        ap (mu (inv x)) (! (ap (λ z → mu z x) (rinv x))) ◃∙
        ap (mu (inv x)) (lam x) ◃∎
          =ₛ⟨ 1 & 3 & ∙-ap-seq (mu (inv x)) (al x (inv x) x ◃∙ ! (ap (λ z → mu z x) (rinv x)) ◃∙ lam x ◃∎) ⟩
        _
          =ₛ₁⟨ 1 & 1 & ap (ap (mu (inv x))) (=ₛ-out zz₁-rot2◃) ⟩
        ! (al (inv x) x (mu (inv x) x) ∙
          ap2 mu (linv x) idp ∙
          lam (mu (inv x) x)) ◃∙
        ap (mu (inv x)) (ap (mu x) (linv x) ∙ rho x) ◃∎
          =ₛ⟨ 0 & 1 & apCommSq2◃' (λ z → ! (al (inv x) x z ∙ ap2 mu (linv x) idp ∙ lam z)) (linv x) ⟩
        ap (λ z → z) (linv x) ◃∙
        ! (al (inv x) x id ∙ ap2 mu (linv x) idp ∙ lam id) ◃∙
        ! (ap (λ z → mu (inv x) (mu x z)) (linv x)) ◃∙
        ap (mu (inv x)) (ap (mu x) (linv x) ∙ rho x) ◃∎
          =ₛ⟨ 1 & 1 & !-∙-seq (al (inv x) x id ◃∙ ap2 mu (linv x) idp ◃∙ lam id ◃∎) ⟩
        ap (λ z → z) (linv x) ◃∙
        ! (lam id) ◃∙
        ! (ap2 mu (linv x) idp) ◃∙
        ! (al (inv x) x id) ◃∙
        ! (ap (λ z → mu (inv x) (mu x z)) (linv x)) ◃∙
        ap (mu (inv x)) (ap (mu x) (linv x) ∙ rho x) ◃∎
          =ₛ₁⟨ 2 & 1 & ap ! (ap2-idp-r mu (linv x)) ⟩
        ap (λ z → z) (linv x) ◃∙
        ! (lam id) ◃∙
        ! (ap (λ z → mu z id) (linv x)) ◃∙
        ! (al (inv x) x id) ◃∙
        ! (ap (λ z → mu (inv x) (mu x z)) (linv x)) ◃∙
        ap (mu (inv x)) (ap (mu x) (linv x) ∙ rho x) ◃∎
          =ₛ⟨ 2 & 1 & hmtpy-nat-∙◃! rho (linv x) ⟩
        ap (λ z → z) (linv x) ◃∙
        ! (lam id) ◃∙
        rho id ◃∙
        ! (ap (λ z → z) (linv x)) ◃∙
        ! (rho (mu (inv x) x)) ◃∙
        ! (al (inv x) x id) ◃∙
        ! (ap (λ z → mu (inv x) (mu x z)) (linv x)) ◃∙
        ap (mu (inv x)) (ap (mu x) (linv x) ∙ rho x) ◃∎
          =ₛ₁⟨ 1 & 1 & ap ! (! (=ₛ-out rho-lam-id-eq)) ⟩
        ap (λ z → z) (linv x) ◃∙
        ! (rho id) ◃∙
        rho id ◃∙
        ! (ap (λ z → z) (linv x)) ◃∙
        ! (rho (mu (inv x) x)) ◃∙
        ! (al (inv x) x id) ◃∙
        ! (ap (λ z → mu (inv x) (mu x z)) (linv x)) ◃∙
        ap (mu (inv x)) (ap (mu x) (linv x) ∙ rho x) ◃∎
          =ₛ₁⟨ 1 & 2 & !-inv-l (rho id) ⟩
        ap (λ z → z) (linv x) ◃∙
        idp ◃∙
        ! (ap (λ z → z) (linv x)) ◃∙
        ! (rho (mu (inv x) x)) ◃∙
        ! (al (inv x) x id) ◃∙
        ! (ap (λ z → mu (inv x) (mu x z)) (linv x)) ◃∙
        ap (mu (inv x)) (ap (mu x) (linv x) ∙ rho x) ◃∎
          =ₛ₁⟨ 0 & 3 & !-inv-r (ap (λ z → z) (linv x)) ⟩
        idp ◃∙
        ! (rho (mu (inv x) x)) ◃∙
        ! (al (inv x) x id) ◃∙
        ! (ap (λ z → mu (inv x) (mu x z)) (linv x)) ◃∙
        ap (mu (inv x)) (ap (mu x) (linv x) ∙ rho x) ◃∎
          =ₛ⟨ 4 & 1 & ap-∙◃ (mu (inv x)) (ap (mu x) (linv x)) (rho x) ⟩
        idp ◃∙
        ! (rho (mu (inv x) x)) ◃∙
        ! (al (inv x) x id) ◃∙
        ! (ap (λ z → mu (inv x) (mu x z)) (linv x)) ◃∙
        ap (mu (inv x)) (ap (mu x) (linv x)) ◃∙
        ap (mu (inv x)) (rho x) ◃∎
          =ₛ₁⟨ 4 & 1 & ∘-ap (mu (inv x)) (mu x) (linv x) ⟩
        _
          =ₛ₁⟨ 3 & 2 & !-inv-l (ap (λ z → mu (inv x) (mu x z)) (linv x)) ⟩
        idp ◃∙
        ! (rho (mu (inv x) x)) ◃∙
        ! (al (inv x) x id) ◃∙
        idp ◃∙
        ap (mu (inv x)) (rho x) ◃∎
          =ₛ₁⟨ =ₛ-out (rho-alid-rho (inv x) x) ⟩
        idp ◃∎ ∎ₛ

    abstract
      zz₁-linv :
        linv x ◃∎
          =ₛ
        ! (ap (mu (inv x)) (rho x)) ◃∙
        al (inv x) x id ◃∙
        ap2 mu (linv x) idp ◃∙
        lam id ◃∎
      zz₁-linv =
        linv x ◃∎
          =ₛ⟨ zz₁-linv-aux ⟩
        ! (al (inv x) x (mu (inv x) x) ∙
          ap2 mu (linv x) idp ∙
          lam (mu (inv x) x)) ◃∙
        ap (mu (inv x))
          (al x (inv x) x ∙
          ! (ap (λ z → mu z x) (rinv x)) ∙
          lam x ∙
          ! (rho x)) ◃∙
        al (inv x) x id ◃∙
        ap2 mu (linv x) idp ◃∙
        lam id ◃∎
          =ₛ⟨ 1 & 1 &
            ap-seq-∙ (mu (inv x))
              (al x (inv x) x ◃∙ ! (ap (λ z → mu z x) (rinv x)) ◃∙ lam x ◃∙ ! (rho x) ◃∎) ⟩
        _
          =ₛ⟨ 0 & 4 & zz₁-linv-suff ⟩
        idp ◃∙
        ap (mu (inv x)) (! (rho x)) ◃∙
        al (inv x) x id ◃∙
        ap2 mu (linv x) idp ◃∙
        lam id ◃∎
          =ₛ₁⟨ 0 & 2 & ap-! (mu (inv x)) (rho x) ⟩
        ! (ap (mu (inv x)) (rho x)) ◃∙
        al (inv x) x id ◃∙
        ap2 mu (linv x) idp ◃∙
        lam id ◃∎ ∎ₛ

    abstract
      zz₁-linv-rot1 :
        ! (lam id) ◃∙
        ! (ap2 mu (linv x) idp) ◃∙
        ! (al (inv x) x id) ◃∙
        ap (mu (inv x)) (rho x) ◃∎
          =ₛ
        ! (linv x) ◃∎
      zz₁-linv-rot1 = post-rotate-in (pre-rotate'-in (pre-rotate'-in (pre-rotate'-in (pre-rotate-out (zz₁-linv)))))

      zz₁-linv-rot2 :
        linv x ◃∙
        ! (lam id) ◃∎
          =ₛ
        ! (ap (mu (inv x)) (rho x)) ◃∙
        al (inv x) x id ◃∙
        ap (λ z → mu z id) (linv x) ◃∎
      zz₁-linv-rot2 =  
        linv x ◃∙
        ! (lam id) ◃∎
          =ₛ⟨ post-rotate'-in (zz₁-linv) ⟩
        ! (ap (mu (inv x)) (rho x)) ◃∙
        al (inv x) x id ◃∙
        ap2 mu (linv x) idp ◃∎
          =ₛ₁⟨ 2 & 1 & ap2-idp-r mu (linv x) ⟩
        ! (ap (mu (inv x)) (rho x)) ◃∙
        al (inv x) x id ◃∙
        ap (λ z → mu z id) (linv x) ◃∎ ∎ₛ
          
