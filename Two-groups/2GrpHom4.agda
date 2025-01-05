{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp
open import 2GrpProps

module 2GrpHom4 where

open CohGrp {{...}}

module MapUnit1 {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  (map : G₁ → G₂) (map-comp : (x y : G₁) → mu (map x) (map y) == map (mu x y))
  (map-id : id == map id)
  (map-al-rot2 :
    (x y z : G₁) →
     ! (al (map x) (map y) (map z)) ◃∎
     =ₛ
     ap (λ v → mu v (map z)) (map-comp x y) ◃∙
     map-comp (mu x y) z ◃∙
     ! (ap map (al x y z)) ◃∙
     ! (map-comp x (mu y z)) ◃∙
     ! (ap (mu (map x)) (map-comp y z)) ◃∎)
  (x : G₁) where
