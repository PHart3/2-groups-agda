{-# OPTIONS --without-K --rewriting --lossy-unification --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import lib.NType2
open import lib.Equivalence2 hiding (linv; rinv)
open import lib.types.LoopSpace
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import Codes
open import Decode3

module Decode6 where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open CohGrp {{...}}

  open import Delooping G

  open WkMagNatIso

  module _ (x y z : G) where

    open decodes x y z
    
    abstract
      loop-comp-decode01 : 
        ! (ap loop (transp-∙ (loop x) (loop y) z)) ◃∙
        ap loop (ap (λ p → transport codes-fst p z) (loop-comp x y)) ◃∙
        ap loop (↯ (transp-codes (mu x y) z)) ◃∙
        ! (loop-comp z (mu x y)) ◃∙
        ! (transp-cst=idf (loop (mu x y)) (loop z)) ◃∎
          =ₛ
        ! (ap loop (transp-∙ (loop x) (loop y) z)) ◃∙
        ap loop (ap (λ p → transport codes-fst p z) (loop-comp x y)) ◃∙
        transport (λ v → loop (transport codes-fst v z) == loop (coe (ap fst (ap codes v)) z))
          (loop-comp x y)
          (ap loop (transp-coe (loop x ∙ loop y) z) ∙
          ap loop (ap (λ q → coe q z) (ap-∘ fst codes (loop x ∙ loop y)))) ◃∙
        ap loop (ap (λ q → coe q z)
          (! ((∙-ap fst (ap codes (loop x)) (ap codes (loop y)) ∙
            ap (ap fst) (∙-Ω-fmap (codes , idp) (loop x) (loop y))) ∙
            ap (ap fst ∘ ap codes) (loop-comp x y)))) ◃∙
        ap loop (ap (λ q → coe q z) (ap2 _∙_ (θ codes-β x) (θ codes-β y))) ◃∙
        ap loop (ap (λ q → coe q z)
          (! (ua-∘e ((λ z → mu z x) , mu-post-iso x) ((λ z → mu z y) , mu-post-iso y)))) ◃∙
        idp ◃∙
        ap loop (app= (ap coe (ua-∘e ((λ v → mu v x) , mu-post-iso x)
          ((λ v → mu v y) , mu-post-iso y))) z) ◃∙
        ap loop (coe-∙ (ua ((λ v → mu v x) , mu-post-iso x)) (ua ((λ v → mu v y) , mu-post-iso y)) z) ◃∙
        ap loop (ap (coe (ua ((λ v → mu v y) , mu-post-iso y)))
          (coe-β ((λ v → mu v x) , mu-post-iso x) z)) ◃∙
        ap loop (coe-β ((λ v → mu v y) , mu-post-iso y) (mu z x)) ◃∙
        ap loop (! (al z x y)) ◃∙
        ! (loop-comp z (mu x y)) ◃∙
        ! (transp-cst=idf (loop (mu x y)) (loop z)) ◃∎
      loop-comp-decode01 = loop-comp-decode0 ∙ₛ loop-comp-decode1
