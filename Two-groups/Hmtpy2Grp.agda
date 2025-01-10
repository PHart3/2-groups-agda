{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth 3 #-}

open import lib.Basics
open import lib.NType2
open import lib.types.LoopSpace
open import 2Grp

module Hmtpy2Grp where

-- homotopy 2-groups of 2-types (i.e., loop spaces)

module _ {i} {X : Type i} where

  open CohGrp

  Loop2Grp : (x : X) {{trX : has-level 1 (x == x)}} → CohGrp (x == x)
  1trunc (Loop2Grp x {{trX}}) = trX
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
    Loop2Grp-instance : {x : X} {{trX : has-level 1 (x == x)}} → CohGrp (x == x)
    Loop2Grp-instance {x} {{trX}} = Loop2Grp x {{trX}}

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
open CohGrpHomStr

module _ {i j} {X₁ : Ptd i} {X₂ : Ptd j}
  {{tr₁ : has-level 2 (de⊙ X₁)}} {{tr₂ : has-level 2 (de⊙ X₂)}} where

  Loop2Grp-map-str : (φ : X₁ ⊙→ X₂) → CohGrpHomStr (Ω-fmap φ)
  map-comp (Loop2Grp-map-str φ) p₁ p₂ = ! (Ω-fmap-∙ φ p₁ p₂)
  map-al (Loop2Grp-map-str (f , idp)) p₁ p₂ p₃ = red-aux1 f p₁ p₂ p₃

  Loop2Grp-map : (φ : X₁ ⊙→ X₂) → CohGrpHom
  map (Loop2Grp-map φ) = Ω-fmap φ
  str (Loop2Grp-map φ) = Loop2Grp-map-str φ


module _ {i j k} {X₁ : Ptd i} {X₂ : Ptd j} {X₃ : Ptd k} {{tr₁ : has-level 2 (de⊙ X₁)}}
  {{tr₂ : has-level 2 (de⊙ X₂)}}  {{tr₃ : has-level 2 (de⊙ X₃)}} where

  Loop2Grp-map-∘ : (φ₂ : X₂ ⊙→ X₃) (φ₁ : X₁ ⊙→ X₂)
    →  CohGrpNatIso (Loop2Grp-map (φ₂ ⊙∘ φ₁)) (Loop2Grp-map φ₂ ∘2G Loop2Grp-map φ₁)
  CohGrpNatIso.θ (Loop2Grp-map-∘ (f₂ , idp) (f₁ , idp)) = λ p → ap-∘ f₂ f₁ p
  CohGrpNatIso.θ-comp (Loop2Grp-map-∘ (f₂ , idp) (f₁ , idp)) = λ p₁ p₂ → red-aux2 f₁ f₂ p₁ p₂

module _ {i} {X : Ptd i} {{tr : has-level 2 (de⊙ X)}} where

  Loop2Grp-map-idf : CohGrpNatIso (Loop2Grp-map (⊙idf X)) (cohgrphom _ {{idf2G}})
  CohGrpNatIso.θ Loop2Grp-map-idf p = ap-idf p
  CohGrpNatIso.θ-comp Loop2Grp-map-idf p₁ p₂ = red-aux3 p₁ p₂

module _ {i j} (G₁ : Type i) {{η₁ : CohGrp G₁}} (G₂ : Type j) {{tr : has-level 1 G₂}} where

  open CohGrp {{...}}

  record 2Grp→-≃ : Type (lmax i j) where
    field
      funs : G₁ → G₂ → G₂
      funs-equiv : (x : G₁) → is-equiv (funs x)
      funs-comp : (x y : G₁) → funs y ∘ funs x ∼ funs (mu x y)
      funs-assoc : (x y z : G₁) (v : G₂) → 
        funs-comp y z (funs x v) ∙
        funs-comp x (mu y z) v
          ==
        ap (funs z) (funs-comp x y v) ∙
        funs-comp (mu x y) z v ∙
        ! (app= (ap funs (al x y z)) v)
        
  open 2Grp→-≃ {{...}} public

  2Grp-≃-to-Loop : {{φ : 2Grp→-≃}} → CohGrpHom {{η₁}} {{Loop2Grp G₂}}
  map (2Grp-≃-to-Loop {{φ}}) x = ua (funs x , funs-equiv x)
  map-comp (str (2Grp-≃-to-Loop {{φ}})) x y = {!!}
  map-al (str (2Grp-≃-to-Loop {{φ}})) x y z = {!!}
