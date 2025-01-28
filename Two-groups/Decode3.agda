{-# OPTIONS --without-K --rewriting --lossy-unification --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import lib.NType2
open import lib.Equivalence2 hiding (linv; rinv)
open import lib.types.LoopSpace
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import Codes
open import Decode0
open import Decode1
open import Decode2

module Decode3 where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open CohGrp {{...}}

  open import Delooping G

  open WkMagNatIso

  module _ (x y z : G) where

    loop-comp-decode0 =
      ! (ap loop (transp-∙ (loop x) (loop y) z)) ◃∙
      ap loop (ap (λ p → transport codes-fst p z) (loop-comp x y)) ◃∙
      ap loop (↯ (transp-codes (mu x y) z)) ◃∙
      ! (loop-comp z (mu x y)) ◃∙
      ! (transp-cst=idf (loop (mu x y)) (loop z)) ◃∎
        =ₛ⟨ 2 & 1 & ap-seq-∙ loop (transp-codes (mu x y) z) ⟩
      ! (ap loop (transp-∙ (loop x) (loop y) z)) ◃∙
      ap loop (ap (λ p → transport codes-fst p z) (loop-comp x y)) ◃∙
      ap loop (transp-coe (loop (mu x y)) z) ◃∙
      ap loop (ap (λ q → coe q z) (ap-∘ fst codes (loop (mu x y)))) ◃∙
      ap loop (ap (λ q → coe q z) (θ codes-β (mu x y))) ◃∙
      ap loop (coe-β ((λ v → mu v (mu x y)) ,  mu-post-iso (mu x y)) z) ◃∙
      ! (loop-comp z (mu x y)) ◃∙
      ! (transp-cst=idf (loop (mu x y)) (loop z)) ◃∎
        =ₛ⟨ 5 & 1 & ap-seq-=ₛ loop (coe-β-mu x y z) ⟩
      ! (ap loop (transp-∙ (loop x) (loop y) z)) ◃∙
      ap loop (ap (λ p → transport codes-fst p z) (loop-comp x y)) ◃∙
      ap loop (transp-coe (loop (mu x y)) z) ◃∙
      ap loop (ap (λ q → coe q z) (ap-∘ fst codes (loop (mu x y)))) ◃∙
      ap loop (ap (λ q → coe q z) (θ codes-β (mu x y))) ◃∙
      ap loop (app= (ap coe (ap ua (pair= (λ= (λ v → al v x y)) prop-has-all-paths-↓))) z)  ◃∙
      ap loop (app= (ap coe (ua-∘e ((λ v → mu v x) , mu-post-iso x)
        ((λ v → mu v y) , mu-post-iso y))) z) ◃∙
      ap loop (coe-∙ (ua ((λ v → mu v x) , mu-post-iso x)) (ua ((λ v → mu v y) , mu-post-iso y)) z) ◃∙
      ap loop (ap (coe (ua ((λ v → mu v y) , mu-post-iso y)))
        (coe-β ((λ v → mu v x) , mu-post-iso x) z)) ◃∙
      ap loop (coe-β ((λ v → mu v y) , mu-post-iso y) (mu z x)) ◃∙
      ap loop (! (al z x y)) ◃∙
      ! (loop-comp z (mu x y)) ◃∙
      ! (transp-cst=idf (loop (mu x y)) (loop z)) ◃∎
        =ₛ⟨ 4 & 1 & code-β-mu-ap2 x y z ⟩
      ! (ap loop (transp-∙ (loop x) (loop y) z)) ◃∙
      ap loop (ap (λ p → transport codes-fst p z) (loop-comp x y)) ◃∙
      ap loop (transp-coe (loop (mu x y)) z) ◃∙
      ap loop (ap (λ q → coe q z) (ap-∘ fst codes (loop (mu x y)))) ◃∙
      ap loop (ap (λ q → coe q z)
        (! ((∙-ap fst (ap codes (loop x)) (ap codes (loop y)) ∙
          ap (ap fst) (∙-Ω-fmap (codes , idp) (loop x) (loop y))) ∙
          ap (ap fst ∘ ap codes) (loop-comp x y)))) ◃∙
      ap loop (ap (λ q → coe q z) (ap2 _∙_ (θ codes-β x) (θ codes-β y))) ◃∙
      ap loop (ap (λ q → coe q z)
        (! (ua-∘e ((λ z → mu z x) , mu-post-iso x) ((λ z → mu z y) , mu-post-iso y)))) ◃∙
      ap loop (! (app= (ap coe (ap ua (pair= (λ= (λ v → al v x y)) prop-has-all-paths-↓))) z)) ◃∙
      ap loop (app= (ap coe (ap ua (pair= (λ= (λ v → al v x y)) prop-has-all-paths-↓))) z) ◃∙
      ap loop (app= (ap coe (ua-∘e ((λ v → mu v x) , mu-post-iso x)
        ((λ v → mu v y) , mu-post-iso y))) z) ◃∙
      ap loop (coe-∙ (ua ((λ v → mu v x) , mu-post-iso x)) (ua ((λ v → mu v y) , mu-post-iso y)) z) ◃∙
      ap loop (ap (coe (ua ((λ v → mu v y) , mu-post-iso y)))
        (coe-β ((λ v → mu v x) , mu-post-iso x) z)) ◃∙
      ap loop (coe-β ((λ v → mu v y) , mu-post-iso y) (mu z x)) ◃∙
      ap loop (! (al z x y)) ◃∙
      ! (loop-comp z (mu x y)) ◃∙
      ! (transp-cst=idf (loop (mu x y)) (loop z)) ◃∎
        =ₛ₁⟨ 7 & 2 &
          ap-!-inv-l loop (app= (ap coe (ap ua (pair= (λ= (λ v → al v x y)) prop-has-all-paths-↓))) z) ⟩
      ! (ap loop (transp-∙ (loop x) (loop y) z)) ◃∙
      ap loop (ap (λ p → transport codes-fst p z) (loop-comp x y)) ◃∙
      ap loop (transp-coe (loop (mu x y)) z) ◃∙
      ap loop (ap (λ q → coe q z) (ap-∘ fst codes (loop (mu x y)))) ◃∙
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
      ! (transp-cst=idf (loop (mu x y)) (loop z)) ◃∎ ∎ₛ

    loop-comp-decode1 =
      ! (ap loop (transp-∙ (loop x) (loop y) z)) ◃∙
      ap loop (ap (λ p → transport codes-fst p z) (loop-comp x y)) ◃∙
      ap loop (transp-coe (loop (mu x y)) z) ◃∙
      ap loop (ap (λ q → coe q z) (ap-∘ fst codes (loop (mu x y)))) ◃∙
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
        =ₛ₁⟨ 2 & 2 & 
          ! (apd-tr
              (λ v → ap loop (transp-coe v z) ∙ ap loop (ap (λ q → coe q z) (ap-∘ fst codes v)))
              (loop-comp x y)) ⟩
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
      ! (transp-cst=idf (loop (mu x y)) (loop z)) ◃∎ ∎ₛ

    abstract
      loop-comp-decode2-pre :
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
          =ₛ
        ap loop (ap (λ q → coe q z)
          (! ((∙-ap fst (ap codes (loop x)) (ap codes (loop y)) ∙
            ap (ap fst) (∙-Ω-fmap (codes , idp) (loop x) (loop y))) ∙
            ap (ap fst ∘ ap codes) (loop-comp x y)))) ◃∙
        ap loop (ap (λ q → coe q z) (ap2 _∙_ (θ codes-β x) (θ codes-β y))) ◃∙
        ap loop (ap (λ q → coe q z)
          (! (ua-∘e ((λ z → mu z x) , mu-post-iso x) ((λ z → mu z y) , mu-post-iso y)))) ◃∙
        ap loop (app= (ap coe (ua-∘e ((λ v → mu v x) , mu-post-iso x)
          ((λ v → mu v y) , mu-post-iso y))) z) ◃∙
        ap loop (coe-∙ (ua ((λ v → mu v x) , mu-post-iso x)) (ua ((λ v → mu v y) , mu-post-iso y)) z) ◃∙
        ap loop (ap (coe (ua ((λ v → mu v y) , mu-post-iso y)))
          (coe-β ((λ v → mu v x) , mu-post-iso x) z)) ◃∙
        ap loop (coe-β ((λ v → mu v y) , mu-post-iso y) (mu z x)) ◃∙
        ap loop (! (al z x y)) ◃∙
        ! (loop-comp z (mu x y)) ◃∙
        ! (transport
            (λ v → transport (_==_ base) v (loop z) == loop z ∙ v)
            (loop-comp x y)
            (transp-cst=idf (loop x ∙ loop y) (loop z))) ◃∎
      loop-comp-decode2-pre =
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
          =ₛ₁⟨ 10 & 1 & ap ! (! (apd-tr (λ v → transp-cst=idf v (loop z)) (loop-comp x y))) ⟩
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
        ! (transport
            (λ v → transport (_==_ base) v (loop z) == loop z ∙ v)
            (loop-comp x y)
            (transp-cst=idf (loop x ∙ loop y) (loop z))) ◃∎
          =ₛ₁⟨ 3 & 2 & idp ⟩
        ap loop (ap (λ q → coe q z)
          (! ((∙-ap fst (ap codes (loop x)) (ap codes (loop y)) ∙
            ap (ap fst) (∙-Ω-fmap (codes , idp) (loop x) (loop y))) ∙
            ap (ap fst ∘ ap codes) (loop-comp x y)))) ◃∙
        ap loop (ap (λ q → coe q z) (ap2 _∙_ (θ codes-β x) (θ codes-β y))) ◃∙
        ap loop (ap (λ q → coe q z)
          (! (ua-∘e ((λ z → mu z x) , mu-post-iso x) ((λ z → mu z y) , mu-post-iso y)))) ◃∙
        ap loop (app= (ap coe (ua-∘e ((λ v → mu v x) , mu-post-iso x)
          ((λ v → mu v y) , mu-post-iso y))) z) ◃∙
        ap loop (coe-∙ (ua ((λ v → mu v x) , mu-post-iso x)) (ua ((λ v → mu v y) , mu-post-iso y)) z) ◃∙
        ap loop (ap (coe (ua ((λ v → mu v y) , mu-post-iso y)))
          (coe-β ((λ v → mu v x) , mu-post-iso x) z)) ◃∙
        ap loop (coe-β ((λ v → mu v y) , mu-post-iso y) (mu z x)) ◃∙
        ap loop (! (al z x y)) ◃∙
        ! (loop-comp z (mu x y)) ◃∙
        ! (transport
            (λ v → transport (_==_ base) v (loop z) == loop z ∙ v)
            (loop-comp x y)
            (transp-cst=idf (loop x ∙ loop y) (loop z))) ◃∎ ∎ₛ
