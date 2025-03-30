{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import lib.NType2
open import lib.Equivalence2 hiding (linv; rinv)
open import lib.types.LoopSpace
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import Codes

module Decode0 where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open CohGrp {{...}}

  open import Delooping G

  open WkMagNatIso

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
