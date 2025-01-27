{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import lib.NType2
open import lib.Equivalence2 hiding (linv; rinv)
open import lib.types.LoopSpace
open import lib.cubical.PathPathOver
open import lib.cubical.PPOverFun
open import 2Magma
open import 2MagMap
open import 2Grp
open import 2GrpAutoEq
open import Hmtpy2Grp
open import Codes

module Decode where

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

    codes-β-mu :
      θ codes-β (mu x y) ◃∎
        =ₛ
      ! ((∙-ap fst (ap codes (loop x)) (ap codes (loop y)) ∙
        ap (ap fst) (∙-Ω-fmap (codes , idp) (loop x) (loop y))) ∙
        ap (ap fst ∘ ap codes) (loop-comp x y)) ◃∙
      ap2 mu (θ codes-β x) (θ codes-β y) ◃∙
      ! (ua-∘e ((λ z → mu z x) , mu-post-iso x) ((λ z → mu z y) , mu-post-iso y)) ◃∙
      ap ua (pair= (λ= (λ v → ! (al v x y))) prop-has-all-paths-↓) ◃∎
    codes-β-mu = {!!}

  module _ (x y z : G) where

    coe-β-mu :
      coe-β ((λ v → mu v (mu x y)) , mu-post-iso (mu x y)) z ◃∎
        =ₛ
      app= (ap coe (ap ua (pair= (λ= (λ v → al v x y)) prop-has-all-paths-↓))) z ◃∙
      app= (ap coe (ua-∘e ((λ v → mu v x) , mu-post-iso x)
        ((λ v → mu v y) , mu-post-iso y))) z ◃∙
      coe-∙ (ua ((λ v → mu v x) , mu-post-iso x)) (ua ((λ v → mu v y) , mu-post-iso y)) z ◃∙
      ap (coe (ua ((λ v → mu v y) , mu-post-iso y)))
        (coe-β ((λ v → mu v x) , mu-post-iso x) z) ◃∙
      coe-β ((λ v → mu v y) , mu-post-iso y) (mu z x) ◃∙
      ! (app= (ap –> (pair= (λ= (λ v → al v x y)) prop-has-all-paths-↓)) z) ◃∎
    coe-β-mu =
      coe-β-∘ ((λ v → mu v x) , mu-post-iso x) ((λ v → mu v y) , mu-post-iso y)
        (pair= (λ= (λ v → al v x y)) prop-has-all-paths-↓) z
{-
    loop-comp-decode : 
      ! (ap loop (transp-∙ (loop x) (loop y) z)) ◃∙
      ap loop (ap (λ p → transport codes-fst p z) (loop-comp x y)) ◃∙
      ap loop (↯ (transp-codes (mu x y) z)) ◃∙
      ! (loop-comp z (mu x y)) ◃∙
      ! (transp-cst=idf (loop (mu x y)) (loop z)) ◃∎
        =ₛ
      ap loop (↯ (transp-codes y (transport codes-fst (loop x) z))) ◃∙
      ! (loop-comp (transport codes-fst (loop x) z) y) ◃∙
        ! (transp-cst=idf (loop y) `(loop (transport codes-fst (loop x) z))) ◃∙
      ap (transport (λ b → base == b) (loop y)) (ap loop (↯ (transp-codes x z))) ◃∙
      ap (transport (λ b → base == b) (loop y)) (! (loop-comp z x)) ◃∙
      ap (transport (λ b → base == b) (loop y)) (! (transp-cst=idf (loop x) (loop z))) ◃∙
      ! (transp-∙ (loop x) (loop y) (loop z)) ◃∙
      ap (λ p → transport (λ b → base == b) p (loop z)) (loop-comp x y) ◃∎
    loop-comp-decode = {!θ-comp (codes-β {{η}})!}
-}
{-

(x₁ y₁ : G) →
!
(lib.Equivalence2.ua-∘e (WkMagHom.map mu-≃-map x₁)
 (WkMagHom.map mu-≃-map y₁))
∙
ap ua
(pair= (λ= (λ v → ! (CohGrp.al η v x₁ y₁))) prop-has-all-paths-↓)
==
!
(ap2 (WkMag.mu (mag (Loop2Grp G))) (WkMagNatIso.θ codes-β x₁)
 (WkMagNatIso.θ codes-β y₁))
∙
(∙-ap (λ r → fst r)
 ((lib.types.LoopSpace.Ω-fmap (codes , idp) ∘ map-wk K₂-loophom) x₁)
 ((lib.types.LoopSpace.Ω-fmap (codes , idp) ∘ map-wk K₂-loophom) y₁)
 ∙
 ap lib.types.Sigma.fst=
 (∙-ap codes (map-wk K₂-loophom x₁) (map-wk K₂-loophom y₁) ∙
  ap (lib.types.LoopSpace.Ω-fmap (codes , idp))
  (map-comp-wk K₂-loophom x₁ y₁)))
∙ WkMagNatIso.θ codes-β (WkMag.mu (mag η) x₁ y₁)

-}
