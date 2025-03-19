{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp

module 2GrpSIP-aux2 {i} (G₁ : Type i) (η₁ : CohGrp G₁) where

  open CohGrp η₁

  tr-inhab : (x y : G₁) →
    ap (λ z → mu z y) (! (! (ap (λ v → v) (rho x))))
      ==
    ! (! (! (ap (λ v → v) (al x id y)))) ∙ ap (mu x) (! (! (ap (λ v → v) (lam y)) ∙ idp))
  tr-inhab x y =
    ap (ap (λ z → mu z y)) (!-!-ap-idf (rho x)) ∙
    tr x y ∙
    ! (ap2 _∙_
        (ap ! (!-!-ap-idf (al x id y)))
        (ap (ap (mu x))
          (!-∙ (! (ap (λ v → v) (lam y))) idp ∙ !-!-ap-idf (lam y))))

  pent-inhab : (w x y z : G₁) →
    ! (! (ap (λ v → v) (al w x (mu y z)))) ∙ ! (! (ap (λ v → v) (al (mu w x) y z)))
      ==
    ap (mu w) (! (! (ap (λ v → v) (al x y z)))) ∙
    ! (! (ap (λ v → v) (al w (mu x y) z))) ∙
    ap (λ v → mu v z) (! (! (ap (λ v → v) (al w x y))))
  pent-inhab w x y z = 
    ap2 _∙_ (!-!-ap-idf (al w x (mu y z))) (!-!-ap-idf (al (mu w x) y z)) ∙
    pent w x y z ∙
    ! (ap3 (λ p₁ p₂ p₃ → p₁ ∙ p₂ ∙ p₃)
         (ap (ap (mu w)) (!-!-ap-idf (al x y z)))
         (!-!-ap-idf (al w (mu x y) z))
         (ap (ap (λ v → mu v z)) (!-!-ap-idf (al w x y))) )

  zz₁-inhab : (x : G₁) →
    ! (! (ap (λ v → v) (lam x)) ∙ idp)
      ==
    ap (λ z → mu z x) (ap (λ v → v) (rinv x)) ∙
    ! (! (! (ap (λ v → v) (al x (inv x) x)))) ∙
    ap (mu x) (! (! (ap (λ v → v) (linv x)))) ∙
    ! (! (ap (λ v → v) (rho x)))
  zz₁-inhab x =
    !-∙ (! (ap (λ v → v) (lam x))) idp ∙
    !-!-ap-idf (lam x) ∙
    zz₁ x ∙
    ! (ap4 (λ p₁ p₂ p₃ p₄ → p₁ ∙ p₂ ∙ p₃ ∙ p₄)
        (ap (ap (λ z → mu z x)) (ap-idf (rinv x)))
        (ap ! (!-!-ap-idf (al x (inv x) x)))
        (ap (ap (mu x)) (!-!-ap-idf (linv x)))
        (!-!-ap-idf (rho x))) 

  zz₂-inhab : (x : G₁) →
    ! (! (! (ap (λ v → v) (lam (inv x))) ∙ idp))
      ==
    ! (! (! (ap (λ v → v) (rho (inv x))))) ∙
    ap (mu (inv x)) (ap (λ v → v) (rinv x)) ∙
    ! (! (ap (λ v → v) (al (inv x) x (inv x)))) ∙
    ap (λ z → mu z (inv x)) (! (! (ap (λ v → v) (linv x))))
  zz₂-inhab x =
    ap ! (!-∙ (! (ap (λ v → v) (lam (inv x)))) idp ∙ !-!-ap-idf (lam (inv x))) ∙
    zz₂ x ∙
    ! (ap4 (λ p₁ p₂ p₃ p₄ → p₁ ∙ p₂ ∙ p₃ ∙ p₄)
        (ap ! (!-!-ap-idf (rho (inv x))))
        (ap (ap (mu (inv x))) (ap-idf (rinv x)))
        (!-!-ap-idf (al (inv x) x (inv x)))
        (ap (ap (λ z → mu z (inv x))) (!-!-ap-idf (linv x))))
