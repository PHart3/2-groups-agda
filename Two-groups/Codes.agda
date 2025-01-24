{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=5 #-}

open import lib.Basics
open import lib.NType2
open import 2Magma
open import 2MagMap
open import 2Grp
open import 2GrpAutoEq
open import Hmtpy2Grp

module Codes where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open CohGrp {{...}}

  open import Delooping G

  codes : K₂ η → 1 -Type i
  codes =
    K₂-rec (G , 1trunc)
      (loop' (2Grp-1Ty-lmap {{η}}))
      (loop-comp' (2Grp-1Ty-lmap {{η}}))
      (loop-assoc' (2Grp-1Ty-lmap {{η}}))

  codes-fst : K₂ η → Type i
  codes-fst = fst ∘ codes

  codes-β-aux :
    WkMagNatIso
      (grphom-forg (Loop2Grp-map (codes , idp)) ∘2Mw K₂-loophom {{η}})
      (loop-2map-forg (G , 1trunc) (2Grp-1Ty-lmap {{η}}))
  WkMagNatIso.θ codes-β-aux =
    loop-βr
      (G , 1trunc)
      (loop' (2Grp-1Ty-lmap {{η}}))
      (loop-comp' (2Grp-1Ty-lmap {{η}}))
      (loop-assoc' (2Grp-1Ty-lmap {{η}}))
  WkMagNatIso.θ-comp codes-β-aux =
    loop-comp-βr
      (G , 1trunc)
      (loop' (2Grp-1Ty-lmap {{η}}))
      (loop-comp' (2Grp-1Ty-lmap {{η}}))
      (loop-assoc' (2Grp-1Ty-lmap {{η}}))

  codes-β :
    WkMagNatIso
      (fst=-2map {{η}} ∘2Mw grphom-forg (Loop2Grp-map (codes , idp)) ∘2Mw K₂-loophom {{η}})
      (maghom-forg (ua-2MagMap G ∘2M mu-≃-map))
  codes-β =
    natiso-tri-∘
      {μ₁ = K₂-loophom {{η}}} {ω₁ = grphom-forg (Loop2Grp-map (codes , idp))} {ω₂ = fst=-2map {{η}}}
      codes-β-aux (fst=-tri {{η}})

  encode : (z : K₂ η) → base == z → codes-fst z
  encode _ p = transport codes-fst p id

  transp-codes : (x y : G) → transport codes-fst (loop x) y =-= mu y x
  transp-codes x y = 
    transport codes-fst (loop x) y
      =⟪ transp-coe {B = codes-fst} (loop x) y ⟫
    coe (ap codes-fst (loop x)) y
      =⟪ ap (λ q → coe q y) (ap-∘ fst codes (loop x)) ⟫
    coe (ap fst (ap codes (loop x))) y
      =⟪ ap (λ q → coe q y) (WkMagNatIso.θ codes-β x) ⟫
    coe ((ua ∘ WkMagHom.map mu-≃-map) x) y
      =⟪ coe-β (WkMagHom.map mu-≃-map x) y ⟫
    mu y x ∎∎

  encode-loop : encode base ∘ loop ∼ idf G
  encode-loop x =
    transport codes-fst (loop x) id
      =⟨ ↯ (transp-codes x id) ⟩
    mu id x
      =⟨ lam x ⟩
    x =∎
  
