{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp

module 2GrpPropsMap where

open CohGrp {{...}}

-- various algebraic lemmas on maps of 2-groups

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  (map : G₁ → G₂)
  (map-comp : (x y : G₁) → mu (map x) (map y) == map (mu x y)) where

  module _
    (map-al : (x y z : G₁) →
      ! (al (map x) (map y) (map z)) ◃∙
      ap (mu (map x)) (map-comp y z) ◃∙
      map-comp x (mu y z) ◃∎
        =ₛ
      ap (λ v → mu v (map z)) (map-comp x y) ◃∙
      map-comp (mu x y) z ◃∙
      ! (ap map (al x y z)) ◃∎)
    (x y z : G₁) where

    abstract
    
      map-al-rot1◃ :
        ! (ap (λ v → mu v (map z)) (map-comp x y)) ◃∙
        ! (al (map x) (map y) (map z)) ◃∎
          =ₛ
        map-comp (mu x y) z ◃∙
        ! (ap map (al x y z)) ◃∙
        ! (map-comp x (mu y z)) ◃∙
        ! (ap (mu (map x)) (map-comp y z)) ◃∎        
      map-al-rot1◃ = post-rotate-in (post-rotate-in (pre-rotate'-in (map-al x y z)))
    
      map-al-rot2◃ :
        map-comp x (mu y z) ◃∙
        ap map (al x y z) ◃∙
        ! (map-comp (mu x y) z) ◃∙
        ! (ap (λ v → mu v (map z)) (map-comp x y)) ◃∎
          =ₛ
        ! (ap (mu (map x)) (map-comp y z)) ◃∙
        al (map x) (map y) (map z) ◃∎
      map-al-rot2◃ =
        post-rotate'-in (post-rotate'-in (post-rotate-out (pre-rotate-in (pre-rotate'-out (map-al x y z)))))

  module _ (map-id : id == map id) where

    module _ (x : G₁) where 
      abstract
        map-id-map-lam : 
          map-id ◃∎
            =ₛ
          ! (! (al id (map x) (inv (map x))) ∙
            ! (ap (mu id) (rinv (map x))) ∙
            rho id) ◃∙
          ap (λ z → mu z (inv (map x))) (
            lam (map x) ∙
            ! (ap map (lam x)) ∙
            ! (map-comp id x)) ◃∙
          ! (al (map id) (map x) (inv (map x))) ◃∙
          ! (ap (mu (map id)) (rinv (map x))) ◃∙
          rho (map id) ◃∎
          →
          ! (ap map (lam x)) ◃∙
          ! (map-comp id x) ◃∙
          ! (ap (λ z → mu z (map x)) map-id) ◃∎
            =ₛ
          ! (lam (map x)) ◃∎
        map-id-map-lam e = post-rotate'-in (pre-rotate-in lemma)
          where
            lemma :
              lam (map x) ◃∙
              ! (ap map (lam x)) ◃∙
              ! (map-comp id x) ◃∎
                =ₛ
              ap (λ z → mu z (map x)) map-id ◃∎
            lemma = =ₛ-in (! (
              ap (ap (λ z → mu z (map x))) (=ₛ-out e) ∙
              <–-inv-r (ap-equiv ((λ z → mu z (map x)) , mu-post-iso (map x)) _ _)
                (lam (map x) ∙ ! (ap map (lam x)) ∙ ! (map-comp id x))))

      -- properties about map-rho

      module _ 
        (map-rho :
          ! (map-comp x id) ◃∎
            =ₛ
          ap map (rho x) ◃∙
          ! (rho (map x)) ◃∙
          ap (mu (map x)) map-id ◃∎) where

        abstract

          map-rho-rot1◃ :
            ! (ap map (rho x)) ◃∙
            ! (map-comp x id) ◃∙
            ! (ap (mu (map x)) map-id) ◃∙
            rho (map x) ◃∎
              =ₛ
            idp ◃∎
          map-rho-rot1◃ =
            ! (ap map (rho x)) ◃∙
            ! (map-comp x id) ◃∙
            ! (ap (mu (map x)) map-id) ◃∙
            rho (map x) ◃∎          
              =ₛ⟨ post-rotate-out (post-rotate'-in (pre-rotate'-in map-rho)) ⟩
            []
              =ₛ₁⟨ idp ⟩
            idp ◃∎ ∎ₛ

          map-rho-rot2◃ :
            ap (mu (map x)) map-id ◃∎
              =ₛ
            rho (map x) ◃∙
            ! (ap map (rho x)) ◃∙
            ! (map-comp x id) ◃∎
          map-rho-rot2◃ = pre-rotate'-out (!ₛ (pre-rotate'-in map-rho))

        abstract
          map-rho-map-id :
            map-id ◃∎
              =ₛ
            ! (al (inv (map x)) (map x) id ∙
              ap2 mu (linv (map x)) idp ∙
              lam id) ◃∙
            ap (mu (inv (map x)))
              (rho (map x) ∙
              ! (ap map (rho x)) ∙
              ! (map-comp x id)) ◃∙
            al (inv (map x)) (map x) (map id) ◃∙
            ap2 mu (linv (map x)) idp ◃∙
            lam (map id) ◃∎
          map-rho-map-id = 
            map-id ◃∎
              =ₛ⟨ =ₛ-in (! (<–-inv-l (ap-equiv (mu (map x) , mu-pre-iso (map x)) _ _) map-id)) ⟩
            ! (al (inv (map x)) (map x) id ∙
              ap2 mu (linv (map x)) idp ∙
              lam id) ◃∙
            ap (mu (inv (map x))) (ap (mu (map x)) map-id) ◃∙
            al (inv (map x)) (map x) (map id) ◃∙
            ap2 mu (linv (map x)) idp ◃∙
            lam (map id) ◃∎
              =ₛ₁⟨ 1 & 1 & ap (ap (mu (inv (map x)))) (=ₛ-out (map-rho-rot2◃)) ⟩
            ! (al (inv (map x)) (map x) id ∙
              ap2 mu (linv (map x)) idp ∙
              lam id) ◃∙
            ap (mu (inv (map x)))
              (rho (map x) ∙ ! (ap map (rho x)) ∙ ! (map-comp x id)) ◃∙
            al (inv (map x)) (map x) (map id) ◃∙
            ap2 mu (linv (map x)) idp ◃∙
            lam (map id) ◃∎ ∎ₛ

      abstract
        map-id-map-rho :
          map-id ◃∎
            =ₛ
          ! (al (inv (map x)) (map x) id ∙
            ap2 mu (linv (map x)) idp ∙
            lam id) ◃∙
          ap (mu (inv (map x)))
            (rho (map x) ∙
            ! (ap map (rho x)) ∙
            ! (map-comp x id)) ◃∙
          al (inv (map x)) (map x) (map id) ◃∙
          ap2 mu (linv (map x)) idp ◃∙
          lam (map id) ◃∎
          →
          ! (map-comp x id) ◃∎
            =ₛ
          ap map (rho x) ◃∙
          ! (rho (map x)) ◃∙
          ap (mu (map x)) map-id ◃∎
        map-id-map-rho e = pre-rotate'-out (pre-rotate-in lemma)
          where
            lemma :
              rho (map x) ◃∙
              ! (ap map (rho x)) ◃∙
              ! (map-comp x id) ◃∎
                =ₛ
              ap (mu (map x)) map-id ◃∎
            lemma = =ₛ-in (! (
              ap (ap (mu (map x))) (=ₛ-out e) ∙
              <–-inv-r (ap-equiv (mu (map x) , mu-pre-iso (map x)) _ _)
                (rho (map x) ∙ ! (ap map (rho x)) ∙ ! (map-comp x id))))

    module _ (map-inv : (x : G₁) → inv (map x) == map (inv x))  where

      abstract
        map-inv-map-linv : (x : G₁) →
          map-inv x ◃∎
            =ₛ
          ! (! (al (inv (map x)) (map x) (inv (map x))) ∙
            ! (ap (mu (inv (map x))) (rinv (map x))) ∙
            rho (inv (map x))) ◃∙
          ap (λ z → mu z (inv (map x)))
            (linv (map x) ∙ map-id ∙ ! (ap map (linv x)) ∙ ! (map-comp (inv x) x)) ◃∙
          ! (al (map (inv x)) (map x) (inv (map x))) ◃∙
          ! (ap (mu (map (inv x))) (rinv (map x))) ◃∙
          rho (map (inv x)) ◃∎
          →
          map-comp (inv x) x ◃∙
          ap map (linv x) ◃∙
          ! map-id ◃∙
          ! (linv (map x)) ◃∎
            =ₛ
          ! (ap (λ z → mu z (map x)) (map-inv x)) ◃∎
        map-inv-map-linv x e = post-rotate'-in (post-rotate'-in (pre-rotate-in (post-rotate-out (post-rotate-out lemma))))
          where
            lemma :
              ap (λ z → mu z (map x)) (map-inv x) ◃∎
                =ₛ
              linv (map x) ◃∙
              map-id ◃∙
              ! (ap map (linv x)) ◃∙
              ! (map-comp (inv x) x) ◃∎
            lemma = =ₛ-in (
              ap (ap (λ z → mu z (map x))) (=ₛ-out e) ∙
              <–-inv-r (ap-equiv ((λ z → mu z (map x)) , mu-post-iso (map x)) _ _)
                (linv (map x) ∙ map-id ∙ ! (ap map (linv x)) ∙ ! (map-comp (inv x) x)))


      -- properties about map-rinv

      module _
        (map-rinv : (x : G₁) →
          ! (ap (mu (map x)) (map-inv x)) ◃∎
            =ₛ
          map-comp x (inv x) ◃∙
          ! (ap map (rinv x)) ◃∙
          ! map-id ◃∙
          rinv (map x) ◃∎)
        (x : G₁) where

        abstract

          map-rinv-rot1◃ :
            ap map (rinv x) ◃∙
            ! (map-comp x (inv x)) ◃∙
            ! (ap (mu (map x)) (map-inv x)) ◃∙
            ! (rinv (map x)) ◃∎
              =ₛ
            ! map-id ◃∎
          map-rinv-rot1◃ = post-rotate'-in (pre-rotate-out (pre-rotate'-in (map-rinv x)))

          map-rinv-rot2◃ :
            map-id ◃∎
              =ₛ
            rinv (map x) ◃∙
            ap (mu (map x)) (map-inv x) ◃∙
            map-comp x (inv x) ◃∙
            ! (ap map (rinv x)) ◃∎
          map-rinv-rot2◃ =
            post-rotate-in (
              post-rotate'-seq-out {q = ap (mu (map x)) (map-inv x) ◃∙ map-comp x (inv x) ◃∎} (
                pre-rotate-out (pre-rotate-out (pre-rotate'-in (map-rinv x)))))

        abstract
          map-rinv-rot3◃ :
            ! (rinv (map x)) ◃∙
            map-id ◃∙
            ap map (rinv x) ◃∙
            ! (map-comp x (inv x)) ◃∎
              =ₛ
            ap (mu (map x)) (map-inv x) ◃∎
          map-rinv-rot3◃ = post-rotate'-in (post-rotate-out (pre-rotate'-in (map-rinv-rot2◃)))

        abstract
          map-rinv-map-inv :
            map-inv x ◃∎
              =ₛ
            ! (al (inv (map x)) (map x) (inv (map x)) ∙
              ap2 mu (linv (map x)) idp ∙
              lam (inv (map x))) ◃∙
            ap (mu (inv (map x)))
              (! (rinv (map x)) ∙ map-id ∙ ap map (rinv x) ∙ ! (map-comp x (inv x))) ◃∙
            al (inv (map x)) (map x) (map (inv x)) ◃∙
            ap2 mu (linv (map x)) idp ◃∙
            lam (map (inv x)) ◃∎
          map-rinv-map-inv = 
            map-inv x ◃∎
              =ₛ⟨ =ₛ-in (! (<–-inv-l (ap-equiv (mu (map x) , mu-pre-iso (map x)) _ _) (map-inv x))) ⟩
            ! (al (inv (map x)) (map x) (inv (map x)) ∙
              ap2 mu (linv (map x)) idp ∙
              lam (inv (map x))) ◃∙
            ap (mu (inv (map x))) (ap (mu (map x)) (map-inv x)) ◃∙
            al (inv (map x)) (map x) (map (inv x)) ◃∙
            ap2 mu (linv (map x)) idp ◃∙
            lam (map (inv x)) ◃∎
              =ₛ₁⟨ 1 & 1 & ap (ap (mu (inv (map x)))) (! (=ₛ-out map-rinv-rot3◃)) ⟩
            ! (al (inv (map x)) (map x) (inv (map x)) ∙
              ap2 mu (linv (map x)) idp ∙
              lam (inv (map x))) ◃∙
            ap (mu (inv (map x)))
              (! (rinv (map x)) ∙ map-id ∙ ap map (rinv x) ∙ ! (map-comp x (inv x))) ◃∙
            al (inv (map x)) (map x) (map (inv x)) ◃∙
            ap2 mu (linv (map x)) idp ◃∙
            lam (map (inv x)) ◃∎ ∎ₛ

      abstract
        map-inv-map-rinv : (x : G₁) →
          map-inv x ◃∎
            =ₛ
          ! (al (inv (map x)) (map x) (inv (map x)) ∙
            ap2 mu (linv (map x)) idp ∙
            lam (inv (map x))) ◃∙
          ap (mu (inv (map x)))
            (! (rinv (map x)) ∙ map-id ∙ ap map (rinv x) ∙ ! (map-comp x (inv x))) ◃∙
          al (inv (map x)) (map x) (map (inv x)) ◃∙
          ap2 mu (linv (map x)) idp ◃∙
          lam (map (inv x)) ◃∎
          →
          map-comp x (inv x) ◃∙
          ! (ap map (rinv x)) ◃∙
          ! map-id ◃∙
          rinv (map x) ◃∎
            =ₛ
          ! (ap (mu (map x)) (map-inv x)) ◃∎
        map-inv-map-rinv x e = pre-rotate-in (post-rotate-out (post-rotate'-in (post-rotate'-in (post-rotate-out lemma))))
          where
            lemma :
              ap (mu (map x)) (map-inv x) ◃∎
                =ₛ
              ! (rinv (map x)) ◃∙
              map-id ◃∙
              ap map (rinv x) ◃∙
              ! (map-comp x (inv x)) ◃∎
            lemma = =ₛ-in (
              ap (ap (mu (map x))) (=ₛ-out e) ∙
              <–-inv-r (ap-equiv (mu (map x) , mu-pre-iso (map x)) _ _)
                (! (rinv (map x)) ∙ map-id ∙ ap map (rinv x) ∙ ! (map-comp x (inv x))))
