{-# OPTIONS --without-K --rewriting --lossy-unification --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import lib.NType2
open import lib.Equivalence2 hiding (linv; rinv)
open import lib.types.LoopSpace
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import Codes
open import Decode13

module Decode14 where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open CohGrp {{...}}

  open import Delooping G

  module _ (x y z : G) where

    abstract
      loop-comp-decode5 :
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
          =ₛ
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
      loop-comp-decode5 =
        long-aux z (loop x) (loop y) (loop z)
          ((λ v → mu v x) , mu-post-iso x) ((λ v → mu v y) , mu-post-iso y)
          (θ codes-β x) (θ codes-β y)
          (coe-β ((λ v → mu v x) , mu-post-iso x) z) (coe-β ((λ v → mu v y) , mu-post-iso y) (mu z x))
          (loop-comp x y) (loop-comp (mu z x) y) (loop-comp z x)
