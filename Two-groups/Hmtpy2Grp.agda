{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.LoopSpace
open import 2Grp

module Hmtpy2Grp where

open CohGrp

-- homotopy 2-groups of 2-types (i.e., loop spaces)

module _ {i} {X : Type i} {{trX : has-level 2 X}} where

  Loop2Grp : (x : X) → CohGrp (x == x)
  1trunc (Loop2Grp x) =  has-level-apply trX x x
  id (Loop2Grp x) = idp
  mu (Loop2Grp x) = _∙_
  lam (Loop2Grp x) p = idp
  rho (Loop2Grp x) = ∙-unit-r
  al (Loop2Grp x) p₁ p₂ p₃ = ! (∙-assoc p₁ p₂ p₃)
  tr (Loop2Grp x) = tri-id
  pent (Loop2Grp x)= pent-id
  inv (Loop2Grp x) = !
  linv (Loop2Grp x) = !-inv-l
  rinv (Loop2Grp x) p = ! (!-inv-r p)
  zz₁ (Loop2Grp x) = zz-id1
  zz₂ (Loop2Grp x) = zz-id2

  instance
    Loop2Grp-instance : {x : X} → CohGrp (x == x)
    Loop2Grp-instance {x} = Loop2Grp x

-- ad-hoc lemmas for Ω's action on  maps, described below
module _ {i j} {X : Type i} {Y : Type j} (f : X → Y) where

  red-aux1 : {x y z w : X} (p₁ : x == y) (p₂ : y == z) (p₃ : z == w) →
    ! (! (∙-assoc (ap f p₁) (ap f p₂) (ap f p₃))) ∙
    ap (_∙_ (ap f p₁)) (! (ap-∙ f p₂ p₃)) ∙
    ! (ap-∙ f p₁ (p₂ ∙ p₃))
    ==
    ap (λ v → v ∙ ap f p₃) (! (ap-∙ f p₁ p₂)) ∙
    ! (ap-∙ f (p₁ ∙ p₂) p₃) ∙
    ! (ap (ap f) (! (∙-assoc p₁ p₂ p₃)))
  red-aux1 idp idp _ = idp

  red-aux2 : ∀ {k} {Z : Type k} (g : Y → Z) {x y z : X}
    (p₁ : x == y) (p₂ : y == z) → 
    ap2 _∙_ (ap-∘ g f p₁) (ap-∘ g f p₂) ∙
    ! (ap-∙ g (ap f p₁) (ap f p₂)) ∙
    ap (ap g) (! (ap-∙ f p₁ p₂))
    ==
    ! (ap-∙ (λ x → g (f x)) p₁ p₂) ∙
    ap-∘ g f (p₁ ∙ p₂)
  red-aux2 g idp idp = idp

module _ {i} {X : Type i} where

  red-aux3 : {x y z : X} (p₁ : x == y) (p₂ : y == z)
    →
    ap2 _∙_ (ap-idf p₁) (ap-idf p₂) ∙ idp
    ==
    ! (ap-∙ (λ x → x) p₁ p₂) ∙ ap-idf (p₁ ∙ p₂)
  red-aux3 idp idp = idp

open CohGrpHom

module _ {i j} {X₁ : Ptd i} {X₂ : Ptd j}
  {{tr₁ : has-level 2 (de⊙ X₁)}} {{tr₂ : has-level 2 (de⊙ X₂)}} where

  Loop2Grp-map : (φ : X₁ ⊙→ X₂) → CohGrpHom {{Loop2Grp (pt X₁)}} {{Loop2Grp (pt X₂)}}
  map (Loop2Grp-map φ) = Ω-fmap φ
  map-comp (Loop2Grp-map φ) p₁ p₂ = ! (Ω-fmap-∙ φ p₁ p₂)
  map-al (Loop2Grp-map (f , idp)) p₁ p₂ p₃ = red-aux1 f p₁ p₂ p₃

module _ {i j k} {X₁ : Ptd i} {X₂ : Ptd j} {X₃ : Ptd k} {{tr₁ : has-level 2 (de⊙ X₁)}}
  {{tr₂ : has-level 2 (de⊙ X₂)}}  {{tr₃ : has-level 2 (de⊙ X₃)}} where

  Loop2Grp-map-∘ : (φ₂ : X₂ ⊙→ X₃) (φ₁ : X₁ ⊙→ X₂)
    →  CohGrpNatIso (Loop2Grp-map (φ₂ ⊙∘ φ₁)) (Loop2Grp-map φ₂ ∘2G Loop2Grp-map φ₁)
  CohGrpNatIso.θ (Loop2Grp-map-∘ (f₂ , idp) (f₁ , idp)) = λ p → ap-∘ f₂ f₁ p
  CohGrpNatIso.θ-comp (Loop2Grp-map-∘ (f₂ , idp) (f₁ , idp)) = λ p₁ p₂ → red-aux2 f₁ f₂ p₁ p₂

module _ {i} {X : Ptd i} {{tr : has-level 2 (de⊙ X)}} where

  Loop2Grp-map-idf : CohGrpNatIso (Loop2Grp-map (⊙idf X)) (id2G)
  CohGrpNatIso.θ Loop2Grp-map-idf p = ap-idf p
  CohGrpNatIso.θ-comp Loop2Grp-map-idf p₁ p₂ = red-aux3 p₁ p₂

module _ {i j} {G₁ : Type i} {{ηR : CohGrp G₁}}
  (G₂ : Type j) (b : G₂) {{_ : has-level 2 G₂}} where
  
--  CohGrpHom {{ηG}} {{Loop2Grp G₂}}

