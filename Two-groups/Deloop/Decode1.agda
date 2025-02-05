{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Sigma
open import lib.Equivalence2 hiding (linv; rinv)
open import lib.types.LoopSpace
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import Codes

module Decode1 where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open CohGrp {{...}}

  open import Delooping G

  open WkMagNatIso

  module _ (x y : G) where

    abstract
      code-β-mu-opt-g : {e : G == G} (p : e == _) →
        p ◃∙
        ap2 _∙_ (θ codes-β x) (θ codes-β y) ◃∙
        (! (ua-∘e ((λ z → mu z x) , mu-post-iso x) ((λ z → mu z y) , mu-post-iso y)) ∙
        ap ua (pair= (λ= (λ v → ! (al v x y))) {b' = mu-post-iso (mu x y)} prop-has-all-paths-↓)) ◃∎
          =ₛ
        p ◃∙
        ap2 _∙_ (θ codes-β x) (θ codes-β y) ◃∙
        ! (ua-∘e ((λ z → mu z x) , mu-post-iso x) ((λ z → mu z y) , mu-post-iso y)) ◃∙
        ap ua (pair= (λ= (λ v → ! (al v x y))) prop-has-all-paths-↓) ◃∎
      code-β-mu-opt-g p =
        p ◃∙
        ap2 _∙_ (θ codes-β x) (θ codes-β y) ◃∙
        (! (ua-∘e ((λ z → mu z x) , mu-post-iso x) ((λ z → mu z y) , mu-post-iso y)) ∙
        ap ua (pair= (λ= (λ v → ! (al v x y))) {b' = mu-post-iso (mu x y)} prop-has-all-paths-↓)) ◃∎
          =ₛ⟨ 2 & 1 & =ₛ-in idp ⟩
        p ◃∙
        ap2 _∙_ (θ codes-β x) (θ codes-β y) ◃∙
        ! (ua-∘e ((λ z → mu z x) , mu-post-iso x) ((λ z → mu z y) , mu-post-iso y)) ◃∙
        ap ua (pair= (λ= (λ v → ! (al v x y))) prop-has-all-paths-↓) ◃∎ ∎ₛ
        
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
