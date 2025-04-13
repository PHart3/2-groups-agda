{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import lib.NType2
open import lib.Equivalence2 hiding (linv; rinv)
open import 2Semigroup
open import 2Grp
open import Hmtpy2Grp
open import Codes

module Decode1 where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open CohGrp {{...}}
  open WkSGrpNatIso

  abstract
    code-β-mu-opt-g : (x y : G) {e : G == G} (p : e == _) →
      p ◃∙
      ap2 _∙_ (θ codes-β x) (θ codes-β y) ◃∙
      (! (ua-∘e ((λ z → mu z x) , mu-post-iso x) ((λ z → mu z y) , mu-post-iso y)) ∙
      ap ua (pair= (λ= (λ v → ! (al v x y))) {b' = mu-post-iso (mu x y)} prop-has-all-paths-↓)) ◃∎
        =ₛ
      p ◃∙
      ap2 _∙_ (θ codes-β x) (θ codes-β y) ◃∙
      ! (ua-∘e ((λ z → mu z x) , mu-post-iso x) ((λ z → mu z y) , mu-post-iso y)) ◃∙
      ap ua (pair= (λ= (λ v → ! (al v x y))) prop-has-all-paths-↓) ◃∎
    code-β-mu-opt-g x y p =
      p ◃∙
      ap2 _∙_ (θ codes-β x) (θ codes-β y) ◃∙
      (! (ua-∘e ((λ z → mu z x) , mu-post-iso x) ((λ z → mu z y) , mu-post-iso y)) ∙
      ap ua (pair= (λ= (λ v → ! (al v x y))) {b' = mu-post-iso (mu x y)} prop-has-all-paths-↓)) ◃∎
        =ₛ⟨ 2 & 1 & =ₛ-in idp ⟩
      p ◃∙
      ap2 _∙_ (θ codes-β x) (θ codes-β y) ◃∙
      ! (ua-∘e ((λ z → mu z x) , mu-post-iso x) ((λ z → mu z y) , mu-post-iso y)) ◃∙
      ap ua (pair= (λ= (λ v → ! (al v x y))) prop-has-all-paths-↓) ◃∎ ∎ₛ
