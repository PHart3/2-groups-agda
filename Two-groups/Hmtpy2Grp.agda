{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import lib.Basics
open import lib.Equivalence2 hiding (linv; rinv)
open import lib.NType2
open import lib.types.Sigma
open import lib.types.LoopSpace
open import 2Magma
open import 2Grp

module Hmtpy2Grp where

-- homotopy 2-groups of 2-types (i.e., loop spaces)

module _ {i} {X : Type i} where

  module _ (x : X) {{trX : has-level 1 (x == x)}} where

    open CohGrp

    Loop2Grp : CohGrp (x == x)
    id Loop2Grp = idp
    mu Loop2Grp = _∙_
    lam Loop2Grp p = idp
    rho Loop2Grp = ∙-unit-r
    al Loop2Grp p₁ p₂ p₃ = ! (∙-assoc p₁ p₂ p₃)
    tr Loop2Grp = tri-id
    pent Loop2Grp = pent-id
    inv Loop2Grp = !
    linv Loop2Grp = !-inv-l
    rinv Loop2Grp p = ! (!-inv-r p)
    zz₁ Loop2Grp = zz-id1
    zz₂ Loop2Grp = zz-id2

  instance
    Loop2Grp-instance : {x : X} {{trX : has-level 1 (x == x)}} → CohGrp (x == x)
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
open WkMagHomStr

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

module _ {i} (G : Type i) {{trG : has-level 1 G}} where

  open WkMag {{...}}
  open WkMagHom
  open WkMagHomStr {{...}}

{-
  ua-2MagMap : WkMagHom {{≃-2Mag G}} {{mag (Loop2Grp G)}}
  map ua-2MagMap = ua
  map-comp (str ua-2MagMap) e₁ e₂ = ! (ua-∘e e₁ e₂)
  map-al (str ua-2MagMap) e₁ e₂ e₃ = =ₛ-out (
    ! (! (∙-assoc (ua e₁) (ua e₂) (ua e₃))) ◃∙
    ap (λ v → ua e₁ ∙ v) (! (ua-∘e e₂ e₃)) ◃∙
    ! (ua-∘e e₁ (e₃ ∘e e₂)) ◃∎
      =ₛ₁⟨ 0 & 1 & !-! (∙-assoc (ua e₁) (ua e₂) (ua e₃))  ⟩
    _
      =ₛ⟨ ua-∘e-al e₁ e₂ e₃ ⟩
    ap (λ v → v ∙ ua e₃) (! (ua-∘e e₁ e₂)) ◃∙
    ! (ua-∘e (e₂ ∘e e₁) e₃) ◃∙
    ! (ap ua (pair= idp (prop-has-all-paths _ _))) ◃∎ ∎ₛ)

  1tr-2MagMap : WkMagHom {{mag (Loop2Grp G)}} {{mag (Loop2Grp {X = 1 -Type i} (G , trG))}}
  map 1tr-2MagMap p = pair= p prop-has-all-paths-↓
  map-comp (str 1tr-2MagMap) p₁ p₂ =
    Σ-∙ {B = has-level 1} {p = p₁} {p' = p₂} prop-has-all-paths-↓ prop-has-all-paths-↓ ∙
    ap (pair= (p₁ ∙ p₂)) (prop-has-all-paths {{↓-level}} _ _)
  map-al (str 1tr-2MagMap) p₁ p₂ p₃ = lemma p₁ p₂ p₃
    where
      lemma : {A₁ A₂ A₃ A₄ : Type i} (q₁ : A₁ == A₂) (q₂ : A₂ == A₃) (q₃ : A₃ == A₄)
        {t₁ : _} {t₂ : _} {t₃ : _} {t₅ : {!!} == {!!} [ has-level 1 ↓ q₂ ]}
        {t₆ : {!!} == {!!} [ has-level 1 ↓ q₃ ]}
        {t₈ : {!!} == {!!} [ has-level 1 ↓ q₁ ]}
        {t₁₀ : {!!} == {!!} [ has-level 1 ↓ (q₂ ∙ q₃) ]}
        {t₇ : t₂ ∙ᵈ t₃ == t₁₀}
        {t₁₁ : {!!}} {t₁₂ : {!!}} {t₁₃ : t₁ ∙ᵈ t₂ == {!!}} {t₁₄ : (p : A₁ == A₄) → {!!}}
        {t₁₅ : {!!}} {t₁₆ : {!!}} {t₁₇ : {!!}} {t₁₈ : {!!}} →
        ! (! (∙-assoc (pair= q₁ t₁) (pair= q₂ t₂) (pair= q₃ t₃))) ∙
        ap (_∙_ (pair= q₁ t₁))
          (Σ-∙ {B = has-level 1} {p = q₂} {p' = q₃} t₅ t₆ ∙
          ap (pair= (q₂ ∙ q₃)) t₇) ∙
        Σ-∙ {B = has-level 1} {p = q₁} {p' = q₂ ∙ q₃} t₈ t₁₀ ∙
        ap (pair= (q₁ ∙ q₂ ∙ q₃)) {!!}
          ==
        ap (λ v → v ∙ pair= q₃ t₃)
          (Σ-∙ {B = has-level 1} {p = q₁} {p' = q₂} {!!} {!!} ∙
          ap (pair= (q₁ ∙ q₂)) t₁₃) ∙
        (Σ-∙ {B = has-level 1} {p = q₁ ∙ q₂} {p' = q₃} {!!} {!!} ∙
        ap (pair= ((q₁ ∙ q₂) ∙ q₃)) {!!}) ∙
        ! (ap (λ p → pair= p (t₁₄ p)) (! (∙-assoc q₁ q₂ q₃)))
      lemma idp idp idp = {!!}
-}
