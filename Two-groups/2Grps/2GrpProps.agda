{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp

module 2GrpProps where

open CohGrp {{...}}

-- properties of all monoidal cats
module _ {i} {G : Type i} {{η : CohGrp G}} where

  module Rotations where

    abstract

      tr-rot : (x y : G) →
        al x id y ◃∙ ap (λ z → mu z y) (rho x) ◃∎
          =ₛ
        ap (mu x) (lam y) ◃∎
      tr-rot x y = pre-rotate-out (=ₛ-in (tr x y))

      pent-rot1 : (w x y z : G) →
        al w x (mu y z) ◃∙ al (mu w x) y z ◃∙ ! (ap (λ v → mu v z) (al w x y)) ◃∎
          =ₛ
        ap (mu w) (al x y z) ◃∙ al w (mu x y) z ◃∎
      pent-rot1 w x y z =
        post-rotate'-seq-in
          {r = al w x (mu y z) ◃∙ al (mu w x) y z ◃∎}
          {q = ap (λ v → mu v z) (al w x y) ◃∎}
          (=ₛ-in (pent w x y z))

      pent-rot2 : (w x y z : G) →
        []
          =ₛ
        ! (al (mu w x) y z) ◃∙
        ! (al w x (mu y z)) ◃∙
        ap (mu w) (al x y z) ◃∙
        al w (mu x y) z ◃∙
        ap (λ u → mu u z) (al w x y) ◃∎
      pent-rot2 w x y z = pre-rotate-in (pre-rotate-in (=ₛ-in (pent w x y z)))

  open Rotations public

  module _ (x y : G) where

    lam-alid-lam0 = 
      ap (mu id) (ap (λ v → mu v y) (! (lam x))) ◃∙
      ap (mu id) (! (al id x y)) ◃∙
      ap (mu id) (lam (mu x y)) ◃∎
        =ₛ₁⟨ 0 & 1 &
          ∘-ap (mu id) (λ z → mu z y) (! (lam x))
          ∙ ap-! (λ z → mu id (mu z y)) (lam x) ⟩
      _
        =ₛ⟨ 0 & 1 & hmtpy-nat-∙◃! (λ z → al id z y) (lam x) ⟩
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
        =ₛ⟨ 1 & 3 & pent-rot1 id id x y ⟩
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

    lam-alid-lam4 :
      ap (mu id) (
        ap (λ v → mu v y) (! (lam x)) ∙
        ! (al id x y) ∙
        lam (mu x y)) ◃∎
        =ₛ
      idp ◃∎
    lam-alid-lam4 =
      ap-seq-∙ (mu id) _ ∙ₛ lam-alid-lam0 ∙ₛ lam-alid-lam1 ∙ₛ lam-alid-lam2 ∙ₛ lam-alid-lam3

    module Lam-alid where

      abstract
        lam-alid-lam :
          ap (λ v → mu v y) (! (lam x)) ◃∙
          ! (al id x y) ◃∙
          lam (mu x y) ◃∎
            =ₛ
          idp ◃∎
        lam-alid-lam = =ₛ-in (ap-equiv-idp muid-iso (=ₛ-out lam-alid-lam4))

    open Lam-alid public

    module Lam-alid-rot where

      abstract
        lam-alid-lam-rot :
          ! (al id x y) ◃∎
            =ₛ
          ap (λ v → mu v y) (lam x) ◃∙
          ! (lam (mu x y)) ◃∎
        lam-alid-lam-rot =
          ! (al id x y) ◃∎
            =ₛ⟨ tri-exch◃ lam-alid-lam ⟩
          _
            =ₛ₁⟨ 0 & 1 & ap ! (ap-! (λ v → mu v y) (lam x)) ∙ !-! (ap (λ v → mu v y) (lam x)) ⟩
          ap (λ v → mu v y) (lam x) ◃∙
          ! (lam (mu x y)) ◃∎ ∎ₛ

    open Lam-alid-rot public

  rho-lam-id-eq0 =
    rho id ◃∎
      =ₛ⟨ =ₛ-in (! (<–-inv-l (ap-equiv ((λ z → mu z id) , idmu-iso) _ _) (rho id))) ⟩
    ! (ap (λ x → x) (! (! (rho (mu id id)))) ∙ idp) ◃∙
    ap (λ x → x) (ap (λ z → mu z id) (rho id)) ◃∙
    ap (λ x → x) (! (! (rho id))) ◃∙
    idp ◃∎
      =ₛ₁⟨ 1 & 1 & ap (ap (λ x → x)) (tr id id) ⟩
    ! (ap (λ x → x) (! (! (rho (mu id id)))) ∙ idp) ◃∙
    ap (λ x → x) (! (al id id id) ∙ ap (mu id) (lam id)) ◃∙
    ap (λ x → x) (! (! (rho id))) ◃∙
    idp ◃∎
      =ₛ⟨ 1 & 1 & !-ap-∙◃ (λ x → x) (al id id id) _ ⟩
    ! (ap (λ x → x) (! (! (rho (mu id id)))) ∙ idp) ◃∙
    ! (ap (λ x → x) (al id id id)) ◃∙
    ap (λ x → x) (ap (mu id) (lam id)) ◃∙
    ap (λ x → x) (! (! (rho id))) ◃∙
    idp ◃∎
      =ₛ₁⟨ 2 & 1 & ap-idf (ap (mu id) (lam id)) ⟩
    ! (ap (λ x → x) (! (! (rho (mu id id)))) ∙ idp) ◃∙
    ! (ap (λ x → x) (al id id id)) ◃∙
    ap (mu id) (lam id) ◃∙
    ap (λ x → x) (! (! (rho id))) ◃∙
    idp ◃∎ ∎ₛ

  rho-lam-id-eq1 =
    ! (ap (λ x → x) (! (! (rho (mu id id)))) ∙ idp) ◃∙
    ! (ap (λ x → x) (al id id id)) ◃∙
    ap (mu id) (lam id) ◃∙
    ap (λ x → x) (! (! (rho id))) ◃∙
    idp ◃∎
      =ₛ⟨ 2 & 1 & hmtpy-nat-∙◃ lam (lam id) ⟩
    _
      =ₛ₁⟨ 3 & 1 & ap-idf (lam id) ⟩
    _
      =ₛ₁⟨ 3 & 2 & !-inv-r (lam id) ⟩
    ! (ap (λ x → x) (! (! (rho (mu id id)))) ∙ idp) ◃∙
    ! (ap (λ x → x) (al id id id)) ◃∙
    lam (mu id id) ◃∙
    idp ◃∙
    ap (λ x → x) (! (! (rho id))) ◃∙
    idp ◃∎ ∎ₛ

  rho-lam-id-eq2 =
    ! (ap (λ x → x) (! (! (rho (mu id id)))) ∙ idp) ◃∙
    ! (ap (λ x → x) (al id id id)) ◃∙
    lam (mu id id) ◃∙
    idp ◃∙
    ap (λ x → x) (! (! (rho id))) ◃∙
    idp ◃∎
      =ₛ₁⟨ 1 & 1 & ap ! (ap-idf (al id id id)) ⟩
    _
      =ₛ⟨ 1 & 2 & pre-rotate-in (lam-alid-lam id id) ⟩
    ! (ap (λ x → x) (! (! (rho (mu id id)))) ∙ idp) ◃∙
    ! (ap (λ v → mu v id) (! (lam id))) ◃∙
    idp ◃∙
    idp ◃∙
    ap (λ x → x) (! (! (rho id))) ◃∙
    idp ◃∎
      =ₛ₁⟨ 0 & 1 &
        ap ! (∙-unit-r (ap (λ x → x) (! (! (rho (mu id id))))) ∙
          ap-idf (! (! (rho (mu id id)))) ∙ !-! (rho (mu id id))) ⟩
    _
      =ₛ₁⟨ 1 & 1 & ap ! (ap-! (λ v → mu v id) (lam id)) ∙ !-! (ap (λ v → mu v id) (lam id)) ⟩
    _
      =ₛ₁⟨ 2 & 4 & ∙-unit-r (ap (λ x → x) (! (! (rho id)))) ∙ ap-idf (! (! (rho id))) ∙ !-! (rho id)  ⟩
    ! (rho (mu id id)) ◃∙
    ap (λ v → mu v id) (lam id) ◃∙
    rho id ◃∎ ∎ₛ

  rho-lam-id-eq3 =
    ! (rho (mu id id)) ◃∙
    ap (λ v → mu v id) (lam id) ◃∙
    rho id ◃∎
      =ₛ₁⟨ apCommSq _ _ rho (lam id) ⟩
    _
      =ₛ₁⟨ ap-idf (lam id) ⟩
    lam id ◃∎ ∎ₛ

  module Rho-lam-id where

    abstract
      rho-lam-id-eq : rho id ◃∎ =ₛ lam id ◃∎
      rho-lam-id-eq = rho-lam-id-eq0 ∙ₛ rho-lam-id-eq1 ∙ₛ rho-lam-id-eq2 ∙ₛ rho-lam-id-eq3

  open Rho-lam-id public

-- properties specific to 2-groups
module _ {i} {G : Type i} {{η : CohGrp G}} (x : G) where

  module ZZ-rot where

    abstract

      zz₁-rot◃ :
        ! (rho x) ◃∙
        ! (ap (mu x) (linv x)) ◃∙
        al x (inv x) x ◃∎
          =ₛ
        ! (lam x) ◃∙
        ap (λ z → mu z x) (rinv x) ◃∎
      zz₁-rot◃ =
        post-rotate-out {q = al x (inv x) x}
          (post-rotate'-in {q = ap (mu x) (linv x)}
            (post-rotate'-in {r = []} {q = rho x}
              (pre-rotate-in (=ₛ-in (zz₁ x)))))

      zz₂-rot◃ :
        ap (mu (inv x)) (rinv x) ◃∙
        al (inv x) x (inv x) ◃∙
        ap (λ z → mu z (inv x)) (linv x) ◃∙
        lam (inv x) ◃∎
          =ₛ
        rho (inv x) ◃∎
      zz₂-rot◃ =
        post-rotate-out
          {p = ap (mu (inv x)) (rinv x) ◃∙
          al (inv x) x (inv x) ◃∙
          ap (λ z → mu z (inv x)) (linv x) ◃∎}
          (!ₛ ((pre-rotate-out {p = rho (inv x)} (=ₛ-in (zz₂ x)))))

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

  open ZZ-rot public

  module ZZ-rinv-suff where

    abstract  
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
          =ₛ₁⟨ 0 & 1 & ap (ap (λ z → mu z (inv x))) (=ₛ-out zz₁-rot◃) ⟩
        ap (λ z → mu z (inv x))
          (! (lam x) ∙ ap (λ z → mu z x) (rinv x)) ◃∙
        (! (al (mu x (inv x)) x (inv x)) ∙
        ! (ap (mu (mu x (inv x))) (rinv x)) ∙
        rho (mu x (inv x))) ◃∎
          =ₛ⟨ 1 & 1 & apCommSq2◃ (λ z → ! (al z x (inv x)) ∙ ! (ap (mu z) (rinv x)) ∙ rho z) (rinv x) ⟩
        _
          =ₑ⟨ 2 & 1 & (! (al id x (inv x)) ◃∙ ! (ap (mu id) (rinv x)) ◃∙ rho id ◃∎) % =ₛ-in idp ⟩
        ap (λ z → mu z (inv x))
          (! (lam x) ∙ ap (λ z → mu z x) (rinv x)) ◃∙
        ! (ap (λ z → mu (mu z x) (inv x)) (rinv x)) ◃∙
        ! (al id x (inv x)) ◃∙
        ! (ap (mu id) (rinv x)) ◃∙
        rho id ◃∙
        ap (λ z → z) (rinv x) ◃∎
          =ₛ⟨ 3 & 1 & hmtpy-nat-∙◃! lam (rinv x) ⟩
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
        ap (λ z → mu z (inv x)) (! (lam x) ∙ ap (λ z → mu z x) (rinv x)) ◃∙
        ! (ap (λ z → mu (mu z x) (inv x)) (rinv x)) ◃∙
        ! (al id x (inv x)) ◃∙
        lam (mu x (inv x)) ◃∙
        idp ◃∎
          =ₛ⟨ 0 & 1 & ap-∙◃ (λ z → mu z (inv x)) (! (lam x)) (ap (λ z → mu z x) (rinv x)) ⟩
        ap (λ z → mu z (inv x)) (! (lam x)) ◃∙
        ap (λ z → mu z (inv x)) (ap (λ z → mu z x) (rinv x)) ◃∙
        ! (ap (λ z → mu (mu z x) (inv x)) (rinv x)) ◃∙
        ! (al id x (inv x)) ◃∙
        lam (mu x (inv x)) ◃∙
        idp ◃∎
          =ₛ₁⟨ 1 & 2 & ap-∘-!-inv-r (λ z → mu z (inv x)) (λ z → mu z x) (rinv x) ⟩
        ap (λ z → mu z (inv x)) (! (lam x)) ◃∙
        idp ◃∙
        ! (al id x (inv x)) ◃∙
        lam (mu x (inv x)) ◃∙
        idp ◃∎
          =ₛ₁⟨ 0 & 4 & =ₛ-out (lam-alid-lam x (inv x)) ⟩
        idp ◃∙ idp ◃∎
          =ₛ₁⟨ idp ⟩
        idp ◃∎ ∎ₛ

  open ZZ-rinv-suff

  module ZZ-rinv where

    abstract
      zz₁-rinv :
        rinv x ◃∎
          =ₛ
        ! (! (al id x (inv x)) ∙ ! (ap (mu id) (rinv x)) ∙ rho id) ◃∙
        ap (λ z → mu z (inv x)) (lam x) ◃∎
      zz₁-rinv =
        rinv x ◃∎
          =ₛ⟨ zz₁-rinv-aux ⟩
        _
          =ₛ⟨ 1 & 1 & ap-∙◃ (λ z → mu z (inv x)) (lam x) (! (rho x) ∙ ! (ap (mu x) (linv x)) ∙ al x (inv x) x) ⟩
        _
          =ₑ⟨ 3 & 3 &
              (! (al (mu x (inv x)) x (inv x)) ∙ ! (ap (mu (mu x (inv x))) (rinv x)) ∙ rho (mu x (inv x))) ◃∎
            % =ₛ-in idp ⟩
        _
          =ₛ⟨ 2 & 2 & zz₁-rinv-suff ⟩
        _
          =ₛ₁⟨ 1 & 2 & ∙-unit-r (ap (λ z → mu z (inv x)) (lam x)) ⟩
        ! (! (al id x (inv x)) ∙ ! (ap (mu id) (rinv x)) ∙ rho id) ◃∙
        ap (λ z → mu z (inv x)) (lam x) ◃∎ ∎ₛ

  open ZZ-rinv public

  abstract
    zz₁-rinv-rot :
      ! (ap (λ z → mu z (inv x)) (lam x)) ◃∙
      ! (al id x (inv x)) ◃∙
      ! (ap (mu id) (rinv x)) ◃∎
        =ₛ
      ! (rinv x) ◃∙
      ! (rho id) ◃∎
    zz₁-rinv-rot = !-!-tri-rot _ _ _ _ zz₁-rinv

