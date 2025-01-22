{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=5 #-}

open import lib.Basics
open import lib.NType2
open import lib.Equivalence2 hiding (linv; rinv)
open import lib.types.Pointed
open import lib.types.LoopSpace
open import lib.types.Truncation
open import lib.cubical.PathPathOver
open import 2Magma
open import 2MagMap
open import 2Grp
open import 2GrpAutoEq
open import Hmtpy2Grp

module LoopDeloop where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open CohGrp {{...}}

  open import Delooping G

  Codes : K₂ η → 1 -Type i
  Codes =
    K₂-rec (G , 1trunc)
      (loop' (2Grp-1Ty-lmap {{η}}))
      (loop-comp' (2Grp-1Ty-lmap {{η}}))
      (loop-assoc' (2Grp-1Ty-lmap {{η}}))

  Codes-fst : K₂ η → Type i
  Codes-fst = fst ∘ Codes

  Codes-β-aux :
    WkMagNatIso
      (grphom-forg (Loop2Grp-map (Codes , idp)) ∘2Mw K₂-loophom {{η}})
      (loop-2map-forg (G , 1trunc) (2Grp-1Ty-lmap {{η}}))
  WkMagNatIso.θ Codes-β-aux =
    loop-βr
      (G , 1trunc)
      (loop' (2Grp-1Ty-lmap {{η}}))
      (loop-comp' (2Grp-1Ty-lmap {{η}}))
      (loop-assoc' (2Grp-1Ty-lmap {{η}}))
  WkMagNatIso.θ-comp Codes-β-aux =
    loop-comp-βr
      (G , 1trunc)
      (loop' (2Grp-1Ty-lmap {{η}}))
      (loop-comp' (2Grp-1Ty-lmap {{η}}))
      (loop-assoc' (2Grp-1Ty-lmap {{η}}))

  Codes-β :
    WkMagNatIso
      (fst=-2map {{η}} ∘2Mw grphom-forg (Loop2Grp-map (Codes , idp)) ∘2Mw K₂-loophom {{η}})
      (maghom-forg (ua-2MagMap G ∘2M mu-≃-map))
  Codes-β =
    natiso-tri-∘
      {μ₁ = K₂-loophom {{η}}} {ω₁ = grphom-forg (Loop2Grp-map (Codes , idp))} {ω₂ = fst=-2map {{η}}}
      Codes-β-aux (fst=-tri {{η}})

  encode : (z : K₂ η) → base == z → Codes-fst z
  encode _ p = transport Codes-fst p id

  encode-loop : encode base ∘ loop ∼ idf G
  encode-loop x =
    transport Codes-fst (loop x) id
      =⟨ transp-coe {B = Codes-fst} (loop x) id ⟩
    coe (ap Codes-fst (loop x)) id
      =⟨ ap (λ q → coe q id) (ap-∘ fst Codes (loop x)) ⟩
    coe (ap fst (ap Codes (loop x))) id
      =⟨ ap (λ q → coe q id) (WkMagNatIso.θ Codes-β x) ⟩
    coe ((ua ∘ WkMagHom.map mu-≃-map) x) id
      =⟨ coe-β (WkMagHom.map mu-≃-map x) id ⟩
    mu id x
      =⟨ lam x ⟩
    x =∎
  
