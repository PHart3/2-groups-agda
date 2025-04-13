{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Sigma
open import lib.Equivalence2 hiding (linv; rinv)
open import lib.types.LoopSpace
open import 2Semigroup
open import 2Grp
open import Hmtpy2Grp
open import Codes

module Decode0 where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open CohGrp {{...}}

  open import Delooping G

  open WkSGrpNatIso

  module _ (x y : G) where

    loop-decode :
      loop (transport codes-fst (loop x) y)
        =-=
      transport (λ z → base == z) (loop x) (loop y)
    loop-decode = 
      loop (transport codes-fst (loop x) y)
        =⟪ ap loop (↯ (transp-codes x y)) ⟫
      loop (mu y x)
        =⟪ ! (loop-comp y x) ⟫
      loop y ∙ loop x
        =⟪ ! (transp-cst=idf (loop x) (loop y)) ⟫
      transport (λ z → base == z) (loop x) (loop y) ∎∎

    abstract
    
      codes-β-mu :
        θ codes-β (mu x y) ◃∎
          =ₛ
        ! ((∙-ap fst (ap codes (loop x)) (ap codes (loop y)) ∙
          ap (ap fst) (∙-Ω-fmap (codes , idp) (loop x) (loop y))) ∙
          ap (ap fst ∘ ap codes) (loop-comp x y)) ◃∙
        ap2 _∙_ (θ codes-β x) (θ codes-β y) ◃∙
        (! (ua-∘e ((λ z → mu z x) , mu-post-iso x) ((λ z → mu z y) , mu-post-iso y)) ∙
        ap ua (pair= (λ= (λ v → ! (al v x y))) prop-has-all-paths-↓)) ◃∎
      codes-β-mu = θ-comp-rot codes-β x y

      coe-β-mu : (z : G) → 
        coe-β ((λ v → mu v (mu x y)) , mu-post-iso (mu x y)) z ◃∎
          =ₛ
        app= (ap coe (ap ua (pair= (λ= (λ v → al v x y)) prop-has-all-paths-↓))) z ◃∙
        app= (ap coe (ua-∘e ((λ v → mu v x) , mu-post-iso x)
          ((λ v → mu v y) , mu-post-iso y))) z ◃∙
        coe-∙ (ua ((λ v → mu v x) , mu-post-iso x)) (ua ((λ v → mu v y) , mu-post-iso y)) z ◃∙
        ap (coe (ua ((λ v → mu v y) , mu-post-iso y)))
          (coe-β ((λ v → mu v x) , mu-post-iso x) z) ◃∙
        coe-β ((λ v → mu v y) , mu-post-iso y) (mu z x) ◃∙
        ! (al z x y) ◃∎
      coe-β-mu z =
        coe-β ((λ v → mu v (mu x y)) , mu-post-iso (mu x y)) z ◃∎
          =ₛ⟨ coe-β-∘ ((λ v → mu v x) , mu-post-iso x) ((λ v → mu v y) , mu-post-iso y)
                (pair= (λ= (λ v → al v x y)) prop-has-all-paths-↓) z ⟩
        app= (ap coe (ap ua (pair= (λ= (λ v → al v x y)) prop-has-all-paths-↓))) z ◃∙
        app= (ap coe (ua-∘e ((λ v → mu v x) , mu-post-iso x)
          ((λ v → mu v y) , mu-post-iso y))) z ◃∙
        coe-∙ (ua ((λ v → mu v x) , mu-post-iso x)) (ua ((λ v → mu v y) , mu-post-iso y)) z ◃∙
        ap (coe (ua ((λ v → mu v y) , mu-post-iso y)))
          (coe-β ((λ v → mu v x) , mu-post-iso x) z) ◃∙
        coe-β ((λ v → mu v y) , mu-post-iso y) (mu z x) ◃∙
        ! (app= (ap –> (pair= (λ= (λ v → al v x y)) prop-has-all-paths-↓)) z) ◃∎
          =ₛ₁⟨ 5 & 1 &
            ap ! (
              ap (ap (λ u → u z)) (fst=-β (λ= (λ v → CohGrp.al η v x y)) prop-has-all-paths-↓) ∙
              app=-β (λ v → CohGrp.al η v x y) z) ⟩
        app= (ap coe (ap ua (pair= (λ= (λ v → al v x y)) prop-has-all-paths-↓))) z ◃∙
        app= (ap coe (ua-∘e ((λ v → mu v x) , mu-post-iso x)
          ((λ v → mu v y) , mu-post-iso y))) z ◃∙
        coe-∙ (ua ((λ v → mu v x) , mu-post-iso x)) (ua ((λ v → mu v y) , mu-post-iso y)) z ◃∙
        ap (coe (ua ((λ v → mu v y) , mu-post-iso y)))
          (coe-β ((λ v → mu v x) , mu-post-iso x) z) ◃∙
        coe-β ((λ v → mu v y) , mu-post-iso y) (mu z x) ◃∙
        ! (al z x y) ◃∎ ∎ₛ
