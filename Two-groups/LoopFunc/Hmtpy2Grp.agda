{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import lib.Equivalence2 hiding (linv; rinv)
open import lib.Univalence2
open import lib.NType2
open import lib.types.Sigma
open import lib.types.LoopSpace
open import 2Semigroup
open import 2SGrpMap
open import 2Grp
open import PostMultMap

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

  module _ {j} {G : Type j} {{η : WkSGrp G}} (x : X) {{trX : has-level 1 (x == x)}} where

    open WkSGrp {{...}}
    
    record Loop2Map : Type (lmax i j) where
      constructor loop2map
      field
        loop' : G → x == x
        loop-comp' : (a b : G) → loop' a ∙ loop' b == loop' (mu a b)
        loop-assoc' : (a b c : G) → 
          ∙-assoc (loop' a) (loop' b) (loop' c) ∙
          ap (λ p → loop' a ∙ p) (loop-comp' b c) ∙
          loop-comp' a (mu b c)
            ==
          ap (λ p → p ∙ loop' c) (loop-comp' a b) ∙
          loop-comp' (mu a b) c ∙'
          ! (ap loop' (al a b c))
    open Loop2Map public
    
    record Loop2Map-∙ : Type (lmax i j) where
      constructor loop2map-∙
      field
        loop∙ : G → x == x
        loop-comp∙ : (a b : G) → loop∙ a ∙ loop∙ b == loop∙ (mu a b)
        loop-assoc' : (a b c : G) → 
          ∙-assoc (loop∙ a) (loop∙ b) (loop∙ c) ∙
          ap (λ p → loop∙ a ∙ p) (loop-comp∙ b c) ∙
          loop-comp∙ a (mu b c)
            ==
          ap (λ p → p ∙ loop∙ c) (loop-comp∙ a b) ∙
          loop-comp∙ (mu a b) c ∙
          ! (ap loop∙ (al a b c))
    open Loop2Map-∙ public

    loop-2map-forg : Loop2Map → WkSGrpWkHom {{η}} {{sgrp (Loop2Grp x)}}
    map-wk (loop-2map-forg f) = loop' f
    map-comp-wk (loop-2map-forg f) = loop-comp' f

    open WkSGrpHom
    open WkSGrpHomStr {{...}}
    
    wksgrp-to-loop : WkSGrpHom {{η}} {{sgrp (Loop2Grp x)}} → Loop2Map
    loop' (wksgrp-to-loop f) = map f
    loop-comp' (wksgrp-to-loop _) = map-comp
    loop-assoc' (wksgrp-to-loop f) a b c = =ₛ-out $
      ∙-assoc (map f a) (map f b) (map f c) ◃∙
      ap (λ p → map f a ∙ p) (map-comp b c) ◃∙
      map-comp a (mu b c) ◃∎
        =ₛ₁⟨ 0 & 1 & ! (!-! (∙-assoc (map f a) (map f b) (map f c))) ⟩
      ! (! (∙-assoc (map f a) (map f b) (map f c))) ◃∙
      ap (λ p → map f a ∙ p) (map-comp b c) ◃∙
      map-comp a (mu b c) ◃∎
        =ₛ⟨ =ₛ-in (map-al a b c) ⟩
      ap (λ p → p ∙ map f c) (map-comp a b) ◃∙
      (map-comp (mu a b) c ∙
      ! (ap (map f) (al a b c))) ◃∎
        =ₛ₁⟨ 1 & 1 & ∙=∙' (map-comp (mu a b) c) (! (ap (map f) (al a b c))) ⟩
      ap (λ p → p ∙ map f c) (map-comp a b) ◃∙
      (map-comp (mu a b) c ∙'
      ! (ap (map f) (al a b c))) ◃∎
        =ₛ₁⟨ idp ⟩
      (ap (λ p → p ∙ map f c) (map-comp a b) ∙
      map-comp (mu a b) c ∙'
      ! (ap (map f) (al a b c))) ◃∎ ∎ₛ

    loop-to-wksgrp : Loop2Map-∙ → WkSGrpHom {{η}} {{sgrp (Loop2Grp x)}}
    map (loop-to-wksgrp f) = loop∙ f
    WkSGrpHomStr.map-comp (str (loop-to-wksgrp f)) = loop-comp∙ f
    WkSGrpHomStr.map-al (str (loop-to-wksgrp f)) a b c = =ₛ-out $
      ! (! (∙-assoc (loop∙ f a) (loop∙ f b) (loop∙ f c))) ◃∙
      ap (_∙_ (loop∙ f a)) (loop-comp∙ f b c) ◃∙
      loop-comp∙ f a (mu b c) ◃∎
        =ₛ₁⟨ 0 & 1 & !-! (∙-assoc (loop∙ f a) (loop∙ f b) (loop∙ f c)) ⟩
      ∙-assoc (loop∙ f a) (loop∙ f b) (loop∙ f c) ◃∙
      ap (_∙_ (loop∙ f a)) (loop-comp∙ f b c) ◃∙
      loop-comp∙ f a (mu b c) ◃∎
        =ₛ⟨ =ₛ-in (loop-assoc' f a b c) ⟩
      ap (λ p → p ∙ loop∙ f c) (loop-comp∙ f a b) ◃∙
      (loop-comp∙ f (WkSGrp.mu η a b) c ∙
      ! (ap (loop∙ f) (WkSGrp.al η a b c))) ◃∎
        =ₛ₁⟨ idp ⟩
      (ap (λ v → v ∙ loop∙ f c) (loop-comp∙ f a b) ∙
      loop-comp∙ f (mu a b) c ∙
      ! (ap (loop∙ f) (al a b c))) ◃∎ ∎ₛ

-- a few ad-hoc lemmas for Ω's action on  maps, described below

module RA1 {i j} {X : Type i} {Y : Type j} (f : X → Y) where

  abstract
    red-aux1 : {x y z w : X} (p₁ : x == y) (p₂ : y == z) (p₃ : z == w) →
      ! (! (∙-assoc (ap f p₁) (ap f p₂) (ap f p₃))) ∙
      ap (_∙_ (ap f p₁)) (∙-ap f p₂ p₃) ∙
      ∙-ap f p₁ (p₂ ∙ p₃)
      ==
      ap (λ v → v ∙ ap f p₃) (∙-ap f p₁ p₂) ∙
      ∙-ap f (p₁ ∙ p₂) p₃ ∙
      ! (ap (ap f) (! (∙-assoc p₁ p₂ p₃)))
    red-aux1 idp idp _ = idp

    red-aux2 : ∀ {k} {Z : Type k} (g : Y → Z) {x y z : X}
      (p₁ : x == y) (p₂ : y == z) → 
      ∙-ap g (ap f p₁) (ap f p₂) ∙
      ap (ap g) (∙-ap f p₁ p₂)
      ==
      ! (ap2 _∙_ (ap-∘ g f p₁) (ap-∘ g f p₂)) ∙
      ∙-ap (g ∘ f) p₁ p₂ ∙
      ap-∘ g f (p₁ ∙ p₂)
    red-aux2 g idp idp = idp

open RA1 public

module RA2 {i} {X : Type i} where

  abstract
    red-aux3 : {x y z : X} (p₁ : x == y) (p₂ : y == z)
      →
      idp
      ==
      ! (ap2 _∙_ (ap-idf p₁) (ap-idf p₂)) ∙ ∙-ap (λ x → x) p₁ p₂ ∙ ap-idf (p₁ ∙ p₂)
    red-aux3 idp idp = idp

open RA2 public

open CohGrpHom
open WkSGrpHomStr

module _ {i j} {X₁ : Ptd i} {X₂ : Ptd j}
  {{tr₁ : has-level 2 (de⊙ X₁)}} {{tr₂ : has-level 2 (de⊙ X₂)}} where

  Loop2Grp-map-str : (φ : X₁ ⊙→ X₂) → CohGrpHomStr (Ω-fmap φ)
  map-comp (Loop2Grp-map-str φ) p₁ p₂ = ∙-Ω-fmap φ p₁ p₂
  map-al (Loop2Grp-map-str (f , idp)) p₁ p₂ p₃ = red-aux1 f p₁ p₂ p₃ 

  Loop2Grp-map : (φ : X₁ ⊙→ X₂) → CohGrpHom
  map (Loop2Grp-map φ) = Ω-fmap φ
  str (Loop2Grp-map φ) = Loop2Grp-map-str φ

module _ {i j k} {X₁ : Ptd i} {X₂ : Ptd j} {X₃ : Ptd k} {{tr₁ : has-level 2 (de⊙ X₁)}}
  {{tr₂ : has-level 2 (de⊙ X₂)}} {{tr₃ : has-level 2 (de⊙ X₃)}} where

  Loop2Grp-map-∘ : (φ₂ : X₂ ⊙→ X₃) (φ₁ : X₁ ⊙→ X₂)
    →  CohGrpNatIso (Loop2Grp-map (φ₂ ⊙∘ φ₁)) (Loop2Grp-map φ₂ ∘2G Loop2Grp-map φ₁)
  WkSGrpNatIso.θ (Loop2Grp-map-∘ (f₂ , idp) (f₁ , idp)) = λ p → ap-∘ f₂ f₁ p
  WkSGrpNatIso.θ-comp (Loop2Grp-map-∘ (f₂ , idp) (f₁ , idp)) = λ p₁ p₂ → red-aux2 f₁ f₂ p₁ p₂

module _ {i} (X : Ptd i) {{tr : has-level 2 (de⊙ X)}} where

  Loop2Grp-map-idf : CohGrpNatIso (Loop2Grp-map (⊙idf X)) (cohgrphom _ {{idf2G}})
  WkSGrpNatIso.θ Loop2Grp-map-idf p = ap-idf p
  WkSGrpNatIso.θ-comp Loop2Grp-map-idf p₁ p₂ = red-aux3 p₁ p₂

module _ {i} (G : Type i) {{trG : has-level 1 G}} where

  open WkSGrp {{...}}
  open WkSGrpHom
  open WkSGrpHomStr {{...}}

  ua-2SGrpMap : WkSGrpHom {{≃-2SGrp G}} {{sgrp (Loop2Grp G)}}
  map ua-2SGrpMap = ua
  map-comp (str ua-2SGrpMap) e₁ e₂ = ! (ua-∘e e₁ e₂)
  map-al (str ua-2SGrpMap) e₁ e₂ e₃ = =ₛ-out $
    ! (! (∙-assoc (ua e₁) (ua e₂) (ua e₃))) ◃∙
    ap (λ v → ua e₁ ∙ v) (! (ua-∘e e₂ e₃)) ◃∙
    ! (ua-∘e e₁ (e₃ ∘e e₂)) ◃∎
      =ₛ₁⟨ 0 & 1 & !-! (∙-assoc (ua e₁) (ua e₂) (ua e₃))  ⟩
    _
      =ₛ⟨ ua-∘e-al e₁ e₂ e₃ ⟩
    ap (λ v → v ∙ ua e₃) (! (ua-∘e e₁ e₂)) ◃∙
    ! (ua-∘e (e₂ ∘e e₁) e₃) ◃∙
    ! (ap ua (pair= idp (prop-has-all-paths _ _))) ◃∎ ∎ₛ

  1tr-2SGrpMap : WkSGrpHom {{sgrp (Loop2Grp G)}} {{sgrp (Loop2Grp {X = 1 -Type i} (G , trG))}}
  map 1tr-2SGrpMap p = pair= p prop-has-all-paths-↓
  map-comp (str 1tr-2SGrpMap) p₁ p₂ =
    Σ-∙ {B = has-level 1} {p = p₁} {p' = p₂} prop-has-all-paths-↓ prop-has-all-paths-↓ ∙
    ap (pair= (p₁ ∙ p₂)) (prop-has-all-paths {{↓-level}} _ _)
  map-al (str 1tr-2SGrpMap) p₁ p₂ p₃ = lemma p₁ p₂ p₃
    where
      lemma : {A₁ A₂ A₃ A₄ : Type i} (q₁ : A₁ == A₂) (q₂ : A₂ == A₃) (q₃ : A₃ == A₄)
        {d₁ : has-level 1 A₁} {d₂ : has-level 1 A₂} {d₃ : has-level 1 A₃} {d₄ : has-level 1 A₄}
        {t₁ : d₁ == d₂ [ has-level 1 ↓ q₁ ]} {t₂ : d₂ == d₃ [ has-level 1 ↓ q₂ ]}
        {t₃ : d₃ == d₄ [ has-level 1 ↓ q₃ ]} {t₈ : d₂ == d₄ [ has-level 1 ↓ (q₂ ∙ q₃) ]}
        {t₄ : d₁ == d₃ [ has-level 1 ↓ (q₁ ∙ q₂) ]} {t₅ : (p : A₁ == A₄) → _}
        {t₆ : t₁ ∙ᵈ t₂ == t₄} {t₇ : t₂ ∙ᵈ t₃ == t₈} {t₉ : t₁ ∙ᵈ t₈ == t₅ (q₁ ∙ q₂ ∙ q₃)}
        {t₁₀ : t₄ ∙ᵈ t₃ == t₅ ((q₁ ∙ q₂) ∙ q₃)} →
        ! (! (∙-assoc (pair= q₁ t₁) (pair= q₂ t₂) (pair= q₃ t₃))) ∙
        ap (_∙_ (pair= q₁ t₁))
          (Σ-∙ {B = has-level 1} {p = q₂} {p' = q₃} t₂ t₃ ∙
          ap (pair= (q₂ ∙ q₃)) t₇) ∙
        Σ-∙ {B = has-level 1} {p = q₁} {p' = q₂ ∙ q₃} t₁ t₈ ∙
        ap (pair= (q₁ ∙ q₂ ∙ q₃)) t₉
          ==
        ap (λ v → v ∙ pair= q₃ t₃)
          (Σ-∙ {B = has-level 1} {p = q₁} {p' = q₂} t₁ t₂ ∙
          ap (pair= (q₁ ∙ q₂)) t₆) ∙
        (Σ-∙ {B = has-level 1} {p = q₁ ∙ q₂} {p' = q₃} t₄ t₃ ∙
        ap (pair= ((q₁ ∙ q₂) ∙ q₃)) t₁₀) ∙
        ! (ap (λ p → pair= p (t₅ p)) (! (∙-assoc q₁ q₂ q₃)))
      lemma {A₁} idp idp idp {t₁ = t₁} {t₂} {t₃} {t₆ = idp} {t₇ = idp} {t₉} {t₁₀} = aux t₁ t₂ t₃ t₉ t₁₀
        where
          aux : {x₁ x₂ x₃ x₄ : has-level 1 A₁}
            (r₁ : x₁ == x₂) (r₂ : x₂ == x₃) (r₃ : x₃ == x₄)
            {z : x₁ == x₄} (r₄ : r₁ ∙ r₂ ∙ r₃ == z) (r₅ : (r₁ ∙ r₂) ∙ r₃ == z)
            →            
            ! (! (∙-assoc (ap (A₁ ,_) r₁) (ap (A₁ ,_) r₂) (ap (A₁ ,_) r₃))) ∙
            ap (_∙_ (ap (A₁ ,_) r₁)) (Σ-∙-aux r₂ r₃ ∙ idp) ∙
            Σ-∙-aux r₁ (r₂ ∙ r₃) ∙ ap (ap (A₁ ,_)) r₄
            ==
            ap (λ v → v ∙ ap (A₁ ,_) r₃) (Σ-∙-aux r₁ r₂ ∙ idp) ∙
            (Σ-∙-aux (r₁ ∙ r₂) r₃ ∙ ap (ap (A₁ ,_)) r₅) ∙ idp
          aux idp idp idp idp r₅ =
            ! (ap (λ p → ap (ap (A₁ ,_)) p ∙ idp)
              (prop-has-all-paths {{=-preserves-level-instance {{=-preserves-level-instance}}}} r₅ idp))

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open CohGrp η

  2Grp-1Ty-map : WkSGrpHom {{sgrp η}} {{sgrp (Loop2Grp (G , 1trunc))}}
  2Grp-1Ty-map = 1tr-2SGrpMap G ∘2M ua-2SGrpMap G ∘2M mu-≃-map

  2Grp-1Ty-lmap : Loop2Map (G , 1trunc)
  2Grp-1Ty-lmap = wksgrp-to-loop (G , 1trunc) 2Grp-1Ty-map

  fst=-2map : WkSGrpWkHom {{sgrp (Loop2Grp (G , 1trunc))}} {{sgrp (Loop2Grp G)}}
  map-wk fst=-2map = fst=
  map-comp-wk fst=-2map p₁ p₂ = ∙-ap fst p₁ p₂
