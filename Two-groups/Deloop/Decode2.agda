{-# OPTIONS --without-K --rewriting --lossy-unification --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Sigma
open import lib.Equivalence2 hiding (linv; rinv)
open import lib.types.LoopSpace
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import Codes
open import Decode0
open import Decode1

module Decode2 where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open CohGrp {{...}}

  open import Delooping G

  open WkMagNatIso

  module _ (x y : G) where

    abstract
    
      code-β-mu-opt :
        θ codes-β (mu x y) ◃∎
          =ₛ
        ! ((∙-ap fst (ap codes (loop x)) (ap codes (loop y)) ∙
          ap (ap fst) (∙-Ω-fmap (codes , idp) (loop x) (loop y))) ∙
          ap (ap fst ∘ ap codes) (loop-comp x y)) ◃∙
        ap2 _∙_ (θ codes-β x) (θ codes-β y) ◃∙
        ! (ua-∘e ((λ z → mu z x) , mu-post-iso x) ((λ z → mu z y) , mu-post-iso y)) ◃∙
        ap ua (pair= (λ= (λ v → ! (al v x y))) prop-has-all-paths-↓) ◃∎
      code-β-mu-opt =
        codes-β-mu x y ∙ₛ
        code-β-mu-opt-g x y
          (! ((∙-ap fst (ap codes (loop x)) (ap codes (loop y)) ∙
            ap (ap fst) (∙-Ω-fmap (codes , idp) (loop x) (loop y))) ∙
            ap (ap fst ∘ ap codes) (loop-comp x y)))

      code-β-mu-ap : (z : G) →
        ap (λ q → coe q z) (θ codes-β (mu x y)) ◃∎
          =ₛ
        ap (λ q → coe q z)
          (! ((∙-ap fst (ap codes (loop x)) (ap codes (loop y)) ∙
            ap (ap fst) (∙-Ω-fmap (codes , idp) (loop x) (loop y))) ∙
            ap (ap fst ∘ ap codes) (loop-comp x y))) ◃∙
        ap (λ q → coe q z) (ap2 _∙_ (θ codes-β x) (θ codes-β y)) ◃∙
        ap (λ q → coe q z)
          (! (ua-∘e ((λ z → mu z x) , mu-post-iso x) ((λ z → mu z y) , mu-post-iso y))) ◃∙
        ! (app= (ap coe (ap ua (pair= (λ= (λ v → al v x y)) prop-has-all-paths-↓))) z) ◃∎
      code-β-mu-ap z =
        ap (λ q → coe q z) (θ codes-β (mu x y)) ◃∎
          =ₛ⟨ ap-seq-=ₛ (λ q → coe q z) code-β-mu-opt ⟩
        ap (λ q → coe q z)
          (! ((∙-ap fst (ap codes (loop x)) (ap codes (loop y)) ∙
            ap (ap fst) (∙-Ω-fmap (codes , idp) (loop x) (loop y))) ∙
            ap (ap fst ∘ ap codes) (loop-comp x y))) ◃∙
        ap (λ q → coe q z) (ap2 _∙_ (θ codes-β x) (θ codes-β y)) ◃∙
        ap (λ q → coe q z)
          (! (ua-∘e ((λ z → mu z x) , mu-post-iso x) ((λ z → mu z y) , mu-post-iso y))) ◃∙
        ap (λ q → coe q z) (ap ua (pair= (λ= (λ v → ! (al v x y))) prop-has-all-paths-↓)) ◃∎
          =ₛ₁⟨ 3 & 1 & 
            ap-∘ (λ u → u z) coe
              (ap ua (pair= (λ= (λ v → ! (al v x y))) prop-has-all-paths-↓)) ∙
            ap (λ q → ap (λ u → u z) (ap coe (ap ua (pair= q prop-has-all-paths-↓))))
              (!-λ= (λ v → al v x y)) ∙
            ap (λ q → ap (λ u → u z) (ap coe (ap ua (pair= (! (λ= (λ v → al {{η}} v x y))) q))))
              (prop-has-all-paths {{↓-level}}_ _) ∙
            ap (λ q → ap (λ u → u z) (ap coe (ap ua q))) (! (Σ-! prop-has-all-paths-↓)) ∙
            ap (ap (λ u → u z) ∘ ap coe) (ap-! ua (pair= (λ= (λ v → al v x y)) prop-has-all-paths-↓)) ∙
            ap (ap (λ u → u z)) (ap-! coe (ap ua (pair= (λ= (λ v → al v x y)) prop-has-all-paths-↓))) ∙
            ap-! (λ u → u z) (ap coe (ap ua (pair= (λ= (λ v → al v x y)) prop-has-all-paths-↓))) ⟩
        ap (λ q → coe q z)
          (! ((∙-ap fst (ap codes (loop x)) (ap codes (loop y)) ∙
            ap (ap fst) (∙-Ω-fmap (codes , idp) (loop x) (loop y))) ∙
            ap (ap fst ∘ ap codes) (loop-comp x y))) ◃∙
        ap (λ q → coe q z) (ap2 _∙_ (θ codes-β x) (θ codes-β y)) ◃∙
        ap (λ q → coe q z)
          (! (ua-∘e ((λ z → mu z x) , mu-post-iso x) ((λ z → mu z y) , mu-post-iso y))) ◃∙
        ! (app= (ap coe (ap ua (pair= (λ= (λ v → al v x y)) prop-has-all-paths-↓))) z) ◃∎ ∎ₛ

      code-β-mu-ap2 : (z : G) →
        ap loop (ap (λ q → coe q z) (θ codes-β (mu x y))) ◃∎
          =ₛ
        ap loop (ap (λ q → coe q z)
          (! ((∙-ap fst (ap codes (loop x)) (ap codes (loop y)) ∙
            ap (ap fst) (∙-Ω-fmap (codes , idp) (loop x) (loop y))) ∙
            ap (ap fst ∘ ap codes) (loop-comp x y)))) ◃∙
        ap loop (ap (λ q → coe q z) (ap2 _∙_ (θ codes-β x) (θ codes-β y))) ◃∙
        ap loop (ap (λ q → coe q z)
          (! (ua-∘e ((λ z → mu z x) , mu-post-iso x) ((λ z → mu z y) , mu-post-iso y)))) ◃∙
        ap loop (! (app= (ap coe (ap ua (pair= (λ= (λ v → al v x y)) prop-has-all-paths-↓))) z)) ◃∎
      code-β-mu-ap2 z = ap-seq-=ₛ loop (code-β-mu-ap z)

      abstract
        loop-comp-decode6 : (z : G) →
          transport
              (λ v → loop (transport codes-fst (loop y) v) == loop v ∙ loop y)
              (! (↯ (transp-codes x z)))
              (ap loop (↯ (transp-codes y (mu z x))) ∙ ! (loop-comp (mu z x) y)) ◃∙
          ! (transp-cst=idf (loop y) (loop (transport codes-fst (loop x) z))) ◃∙
          ap (transport (λ b → base == b) (loop y)) (ap loop (↯ (transp-codes x z))) ◃∙
          ap (transport (λ b → base == b) (loop y)) (! (loop-comp z x)) ◃∙
          ap (transport (λ b → base == b) (loop y)) (! (transp-cst=idf (loop x) (loop z))) ◃∙
          ! (transp-∙ (loop x) (loop y) (loop z)) ◃∙
          ap (λ p → transport (λ b → base == b) p (loop z)) (loop-comp x y) ◃∎
            =ₛ
          ap loop (↯ (transp-codes y (transport codes-fst (loop x) z))) ◃∙
          ! (loop-comp (transport codes-fst (loop x) z) y) ◃∙
          ! (transp-cst=idf (loop y) (loop (transport codes-fst (loop x) z))) ◃∙
          ap (transport (λ b → base == b) (loop y)) (ap loop (↯ (transp-codes x z))) ◃∙
          ap (transport (λ b → base == b) (loop y)) (! (loop-comp z x)) ◃∙
          ap (transport (λ b → base == b) (loop y)) (! (transp-cst=idf (loop x) (loop z))) ◃∙
          ! (transp-∙ (loop x) (loop y) (loop z)) ◃∙
          ap (λ p → transport (λ b → base == b) p (loop z)) (loop-comp x y) ◃∎
        loop-comp-decode6 z = 
          transport
            (λ v → loop (transport codes-fst (loop y) v) == loop v ∙ loop y)
            (! (↯ (transp-codes x z)))
            (ap loop (↯ (transp-codes y (mu z x))) ∙ ! (loop-comp (mu z x) y)) ◃∙
          ! (transp-cst=idf (loop y) (loop (transport codes-fst (loop x) z))) ◃∙
          ap (transport (λ b → base == b) (loop y)) (ap loop (↯ (transp-codes x z))) ◃∙
          ap (transport (λ b → base == b) (loop y)) (! (loop-comp z x)) ◃∙
          ap (transport (λ b → base == b) (loop y)) (! (transp-cst=idf (loop x) (loop z))) ◃∙
          ! (transp-∙ (loop x) (loop y) (loop z)) ◃∙
          ap (λ p → transport (λ b → base == b) p (loop z)) (loop-comp x y) ◃∎
            =ₑ⟨ 0 & 1 &
              (ap loop (↯ (transp-codes y (transport codes-fst (loop x) z))) ◃∙
              ! (loop-comp (transport codes-fst (loop x) z) y) ◃∎) %
              =ₛ-in $
                apd-tr (λ v → ap loop (↯ (transp-codes y v)) ∙ ! (loop-comp v y))
                  (! (↯ (transp-codes x z))) ⟩
          ap loop (↯ (transp-codes y (transport codes-fst (loop x) z))) ◃∙
          ! (loop-comp (transport codes-fst (loop x) z) y) ◃∙
          ! (transp-cst=idf (loop y) (loop (transport codes-fst (loop x) z))) ◃∙
          ap (transport (λ b → base == b) (loop y)) (ap loop (↯ (transp-codes x z))) ◃∙
          ap (transport (λ b → base == b) (loop y)) (! (loop-comp z x)) ◃∙
          ap (transport (λ b → base == b) (loop y)) (! (transp-cst=idf (loop x) (loop z))) ◃∙
          ! (transp-∙ (loop x) (loop y) (loop z)) ◃∙
          ap (λ p → transport (λ b → base == b) p (loop z)) (loop-comp x y) ◃∎ ∎ₛ
