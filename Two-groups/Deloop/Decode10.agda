{-# OPTIONS --without-K --rewriting --lossy-unification --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import lib.NType2
open import lib.Equivalence2 hiding (linv; rinv)
open import lib.types.LoopSpace
open import 2Semigroup
open import 2Grp
open import Hmtpy2Grp
open import Codes
open import Decode8
open import Decode9

module Decode10 where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open CohGrp {{...}}

  open import Delooping G

  open WkSGrpNatIso

  module _ (x y z : G) where

    abstract
      loop-comp-decode04 :
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
        ap loop (coe-∙ (ua ((λ v → mu v x) , mu-post-iso x)) (ua ((λ v → mu v y) , mu-post-iso y)) z) ◃∙
        ap loop (ap (coe (ua ((λ v → mu v y) , mu-post-iso y)))
          (coe-β ((λ v → mu v x) , mu-post-iso x) z)) ◃∙
        ap loop (coe-β ((λ v → mu v y) , mu-post-iso y) (mu z x)) ◃∙
        ! (loop-comp (mu z x) y) ◃∙
        ! (ap (λ p → p ∙ loop y) (loop-comp z x)) ◃∙
        ∙-assoc (loop z) (loop x) (loop y) ◃∙
        ap (λ p → loop z ∙ p) (loop-comp x y) ◃∙
        ! (transport
            (λ v → transport (_==_ base) v (loop z) == loop z ∙ v)
            (loop-comp x y)
            (transp-cst=idf (loop x ∙ loop y) (loop z))) ◃∎
      loop-comp-decode04 = loop-comp-decode03 x y z ∙ₛ loop-comp-decode4 x y z
