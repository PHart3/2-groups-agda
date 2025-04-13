{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=5 #-}

open import lib.Basics
open import lib.NType2
open import 2Semigroup
open import 2SGrpMap
open import 2Grp
open import PostMultMap
open import Hmtpy2Grp
open import Hmtpy2Grp2

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
    WkSGrpNatIso
      (grphom-forg (Loop2Grp-map (codes , idp)) ∘2Mw K₂-loophom {{η}})
      (loop-2map-forg (G , 1trunc) (2Grp-1Ty-lmap {{η}}))
  WkSGrpNatIso.θ codes-β-aux =
    loop-βr
      (G , 1trunc)
      (loop' (2Grp-1Ty-lmap {{η}}))
      (loop-comp' (2Grp-1Ty-lmap {{η}}))
      (loop-assoc' (2Grp-1Ty-lmap {{η}}))
  WkSGrpNatIso.θ-comp codes-β-aux =
    loop-comp-βr
      (G , 1trunc)
      (loop' (2Grp-1Ty-lmap {{η}}))
      (loop-comp' (2Grp-1Ty-lmap {{η}}))
      (loop-assoc' (2Grp-1Ty-lmap {{η}}))

  codes-β :
    WkSGrpNatIso
      ((fst=-2map {{η}} ∘2Mw grphom-forg (Loop2Grp-map (codes , idp))) ∘2Mw K₂-loophom {{η}})
      (sgrphom-forg (ua-2SGrpMap G ∘2M mu-≃-map))
  codes-β =
    (fst=-2map {{η}} ∘2Mw grphom-forg (Loop2Grp-map (codes , idp))) ∘2Mw K₂-loophom {{η}}
      =⟦ !ʷ (assoc-wksgrphom (fst=-2map {{η}}) (grphom-forg (Loop2Grp-map (codes , idp))) (K₂-loophom {{η}})) ⟧
    fst=-2map {{η}} ∘2Mw grphom-forg (Loop2Grp-map (codes , idp)) ∘2Mw K₂-loophom {{η}}
      =⟦ natiso-tri-∘
           {μ₁ = K₂-loophom {{η}}} {ω₁ = grphom-forg (Loop2Grp-map (codes , idp))} {ω₂ = fst=-2map {{η}}}
           codes-β-aux (fst=-tri {{η}}) ⟧
    sgrphom-forg (ua-2SGrpMap G ∘2M mu-≃-map) ∎ₙ

  encode : (z : K₂ η) → base == z → codes-fst z
  encode _ p = transport codes-fst p id

  transp-codes : (x y : G) → transport codes-fst (loop x) y =-= mu y x
  transp-codes x y = 
    transport codes-fst (loop x) y
      =⟪ transp-coe {B = codes-fst} (loop x) y ⟫
    coe (ap codes-fst (loop x)) y
      =⟪ ap (λ q → coe q y) (ap-∘ fst codes (loop x)) ⟫
    coe (ap fst (ap codes (loop x))) y
      =⟪ ap (λ q → coe q y) (WkSGrpNatIso.θ codes-β x) ⟫
    coe ((ua ∘ WkSGrpHom.map mu-≃-map) x) y
      =⟪ coe-β (WkSGrpHom.map mu-≃-map x) y ⟫
    mu y x ∎∎

  encode-loop : encode base ∘ loop ∼ idf G
  encode-loop x =
    transport codes-fst (loop x) id
      =⟨ ↯ (transp-codes x id) ⟩
    mu id x
      =⟨ lam x ⟩
    x =∎
  
