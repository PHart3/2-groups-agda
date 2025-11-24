{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.LoopSpace
open import 2Grp
open import 2GrpMap
open import Bicategory
open import Biequiv
open import 2Grp-bc
open import Ptd-bc
open import Hmtpy2Grp
open import LoopFunctor-conv
open import Delooping
open import LoopK-hom
open import KFunctor
open import KFunctor-idf
open import KFunctor-comp
open import KFunctor-conv-unit
open import KFunctor-conv-assoc
open import SqLoopK
open import LoopK-PT-assoc
open import LoopK-PT-unit
open import SqKLoop
open import KLoop-PT-assoc
open import KLoop-PT-unit
open import KLoop-adjeq
open import LoopK-adjeq

-- Final theorem: biequivalence between 2-groups and pointed connected 2-types

module Biequiv-main where

  open PsfunctorStr
  open Psfunctor
  open Pstrans
  open BiequivStr-inst

  2Grp-Ptd02-bieq : (i : ULevel) → BiequivStr (2grp-bicat i) (Ptd02-bicat i)

  -- pseudofunctor from 2-groups to pointed connected 2-types
  map-pf (Ψ₁ (2Grp-Ptd02-bieq _)) = λ (G , η) → ⊙[ K₂ G η , base G {{η}} ] , ((K₂-is-conn G {{η}}) , (K₂-is-2type G {{η}}))
  F₁ (str-pf (Ψ₁ (2Grp-Ptd02-bieq _))) {_ , η₁} {_ , η₂} = K₂-action-hom {{η₁}} {{η₂}}
  F-id₁ (str-pf (Ψ₁ (2Grp-Ptd02-bieq _))) = λ (_ , η) → ⊙-crd∼-to-== (K₂-map-idf {{η}})
  F-◻ (str-pf (Ψ₁ (2Grp-Ptd02-bieq _))) {_ , η₁} {_ , η₂} {_ , η₃} =
    λ (cohgrphom _ {{σ₁}}) (cohgrphom _ {{σ₂}}) → ⊙-crd∼-to-== (K₂-map-∘ {{η₁}} {{η₂}} {{η₃}} σ₁ σ₂)
  F-ρ (str-pf (Ψ₁ (2Grp-Ptd02-bieq _))) {_ , η₁} {_ , η₂} = K₂-ρ {{η₁}} {{η₂}}
  F-λ (str-pf (Ψ₁ (2Grp-Ptd02-bieq _))) {_ , η₁} {_ , η₂}= K₂-λ {{η₁}} {{η₂}}
  F-α (str-pf (Ψ₁ (2Grp-Ptd02-bieq _))) {_ , η₁} {_ , η₂} {_ , η₃} {_ , η₄} = K₂-α {{η₁}} {{η₂}} {{η₃}} {{η₄}}

  -- pseudofunctor from pointed connected 2-types to 2-groups
  map-pf (Ψ₂ (2Grp-Ptd02-bieq _)) = λ (X , _ , tr) → (Ω X) , (Loop2Grp (pt X) {{has-level-apply tr (pt X) (pt X)}})
  F₁ (str-pf (Ψ₂ (2Grp-Ptd02-bieq _))) {_ , _ , tr₁} {_ , _ , tr₂} = Loop2Grp-map {{tr₁}} {{tr₂}}
  F-id₁ (str-pf (Ψ₂ (2Grp-Ptd02-bieq _))) = λ (X , _ , tr) →
    natiso2G-to-== {{Loop2Grp (pt X) {{has-level-apply tr (pt X) (pt X)}}}} {{Loop2Grp (pt X) {{has-level-apply tr (pt X) (pt X)}}}}
      (Loop2Grp-map-idf X {{tr}})
  F-◻ (str-pf (Ψ₂ (2Grp-Ptd02-bieq _))) {X₁ , _ , tr₁} {_ , _ , tr₂} {X₃ , _ , tr₃} = λ f g →
    natiso2G-to-== {{Loop2Grp (pt X₁) {{has-level-apply tr₁ (pt X₁) (pt X₁)}}}} {{Loop2Grp (pt X₃) {{has-level-apply tr₃ (pt X₃) (pt X₃)}}}}
      (Loop2Grp-map-∘ {{tr₁}} {{tr₂}} {{tr₃}} g f)
  F-ρ (str-pf (Ψ₂ (2Grp-Ptd02-bieq _))) {_ , _ , tr₁} {_ , _ , tr₂} = Ω-ρ {{tr₁}} {{tr₂}}
  F-λ (str-pf (Ψ₂ (2Grp-Ptd02-bieq _))) {_ , _ , tr₁} {_ , _ , tr₂} = Ω-λ {{tr₁}} {{tr₂}}
  F-α (str-pf (Ψ₂ (2Grp-Ptd02-bieq _))) {_ , _ , tr₁} {_ , _ , tr₂} {_ , _ , tr₃} {_ , _ , tr₄} = Ω-α {{tr₁}} {{tr₂}} {{tr₃}} {{tr₄}}

  -- pseudotransformation from K₂ ∘ Ω to identity
  η₀ (fst (ε (2Grp-Ptd02-bieq _))) (X , _ , tr) =
    K₂-rec-hom {{Loop2Grp (pt X) {{has-level-apply tr (pt X) (pt X)}}}} {{tr}} (pt X)
      (idf2G {{Loop2Grp (pt X) {{has-level-apply tr (pt X) (pt X)}}}})
  η₁ (fst (ε (2Grp-Ptd02-bieq _))) {X₁ , _ , tr₁} {X₂ , _ , tr₂} = λ f → ⊙-crd∼-to-== (sq-KΩ {{tr₁}} {{tr₂}} (pt X₁) (pt X₂) f)
  coher-unit (fst (ε (2Grp-Ptd02-bieq _))) {_ , _ , tr} = KLoop-coher-unit {{tr}}
  coher-assoc (fst (ε (2Grp-Ptd02-bieq _))) {_ , _ , tr₁} {_ , _ , tr₂} {_ , _ , tr₃} = KLoop-coher-assoc {{tr₁}} {{tr₂}} {{tr₃}}

  -- pseudotransformation from identity to Ω ∘ K₂
  η₀ (fst (η (2Grp-Ptd02-bieq _))) (G , η) = K₂-loopmap G {{η}}
  η₁ (fst (η (2Grp-Ptd02-bieq _))) {_ , η₁} {G₂ , η₂} = λ f →
    natiso2G-to-== {{η₁}} {{Loop2Grp (base G₂ {{η₂}}) {{has-level-apply (K₂-is-2type G₂ {{η₂}}) (base G₂ {{η₂}}) (base G₂ {{η₂}})}}}}
      (sq-ΩK {{η₁}} {{η₂}} (CohGrpHom.str {{η₁}} {{η₂}} f))
  coher-unit (fst (η (2Grp-Ptd02-bieq _))) {_ , η} = LoopK-coher-unit {{η}}
  coher-assoc (fst (η (2Grp-Ptd02-bieq _))) {_ , η₁} {_ , η₂} {_ , η₃} = LoopK-coher-assoc {{η₁}} {{η₂}} {{η₃}}

  -- levelwise adjoint equivalence
  snd (ε (2Grp-Ptd02-bieq _)) (_ , cX , tX) = KLoop-adjeq-str {{cX}} {{tX}}
  snd (η (2Grp-Ptd02-bieq _)) (_ , η) = Loop-adjeq-str {{η}}
