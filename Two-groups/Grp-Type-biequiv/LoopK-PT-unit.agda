{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=5 --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.LoopSpace
open import 2Grp
open import 2Semigroup
open import 2SGrpMap
open import 2GrpMap
open import 2GrpMap-conv
open import NatIso2G
open import Hmtpy2Grp
open import KFunctor
open import KFunctor-idf
open import LoopFunctor-ap
open import SqLoopK
open import LoopK-ptr-idf

-- unit coherence for pseudotransformation from identity to Ω ∘ K₂

module LoopK-PT-unit where

module _ {i} {G : Type i} {{η : CohGrp G}} where 

  open import Delooping G

  abstract
    LoopK-coher-unit :
      natiso2G-to-== (unit-wksgrphom-l (grphom-forg K₂-loopmap)) ∙
      ap (λ m → m ∘2G K₂-loopmap)
        (! (ap Loop2Grp-map (⊙-crd∼-to-== (K₂-map-idf {{η}})) ∙
        natiso2G-to-== (Loop2Grp-map-idf ⊙[ K₂ η , base ]))) ∙
      natiso2G-to-== (sq-ΩK (idf2G {{η}})) ∙
      idp
        ==
      natiso2G-to-== (unit-wksgrphom-r (grphom-forg K₂-loopmap))
    LoopK-coher-unit = =ₛ-out $
      natiso2G-to-== (unit-wksgrphom-l (grphom-forg K₂-loopmap)) ◃∙
      ap (λ m → m ∘2G K₂-loopmap)
        (! (ap Loop2Grp-map (⊙-crd∼-to-== (K₂-map-idf {{η}})) ∙
        natiso2G-to-== (Loop2Grp-map-idf ⊙[ K₂ η , base ]))) ◃∙
      natiso2G-to-== (sq-ΩK (idf2G {{η}})) ◃∙
      idp ◃∎
        =ₛ₁⟨ 1 & 1 & ap-! (λ m → m ∘2G K₂-loopmap) $
          ap Loop2Grp-map (⊙-crd∼-to-== (K₂-map-idf {{η}})) ∙ natiso2G-to-== (Loop2Grp-map-idf ⊙[ K₂ η , base ]) ⟩
      natiso2G-to-== (unit-wksgrphom-l (grphom-forg K₂-loopmap)) ◃∙
      ! (ap (λ m → m ∘2G K₂-loopmap)
          (ap Loop2Grp-map (⊙-crd∼-to-== (K₂-map-idf {{η}})) ∙
          natiso2G-to-== (Loop2Grp-map-idf ⊙[ K₂ η , base ]))) ◃∙
      natiso2G-to-== (sq-ΩK (idf2G {{η}})) ◃∙
      idp ◃∎
        =ₛ⟨ 1 & 1 & !-=ₛ $
          ap-∙◃ (λ m → m ∘2G K₂-loopmap)
            (ap Loop2Grp-map (⊙-crd∼-to-== (K₂-map-idf {{η}})))
            (natiso2G-to-== (Loop2Grp-map-idf ⊙[ K₂ η , base ])) ⟩
      natiso2G-to-== (unit-wksgrphom-l (grphom-forg K₂-loopmap)) ◃∙
      ! (ap (λ m → m ∘2G K₂-loopmap) (natiso2G-to-== (Loop2Grp-map-idf ⊙[ K₂ η , base ]))) ◃∙
      ! (ap (λ m → m ∘2G K₂-loopmap) (ap Loop2Grp-map (⊙-crd∼-to-== K₂-map-idf))) ◃∙
      natiso2G-to-== (sq-ΩK idf2G) ◃∙
      idp ◃∎
        =ₛ₁⟨ 1 & 1 &
          ap ! (! (whisk2G-conv-r (Loop2Grp-map-idf ⊙[ K₂ η , base ]))) ∙
          ! (natiso2G-! (natiso-whisk-r (Loop2Grp-map-idf ⊙[ K₂ η , base ]))) ⟩
      natiso2G-to-== (unit-wksgrphom-l (grphom-forg K₂-loopmap)) ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-r (Loop2Grp-map-idf ⊙[ K₂ η , base ]))) ◃∙
      ! (ap (λ m → m ∘2G K₂-loopmap) (ap Loop2Grp-map (⊙-crd∼-to-== K₂-map-idf))) ◃∙
      natiso2G-to-== (sq-ΩK idf2G) ◃∙
      idp ◃∎
        =ₛ₁⟨ 2 & 1 & ap ! (ap (ap (λ m → m ∘2G K₂-loopmap)) (Ω-fmap-ap-pres (K₂-map-idf))) ⟩
      natiso2G-to-== (unit-wksgrphom-l (grphom-forg K₂-loopmap)) ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-r (Loop2Grp-map-idf ⊙[ K₂ η , base ]))) ◃∙
      ! (ap (λ m → m ∘2G K₂-loopmap) (natiso2G-to-== (Loop2Grp-map-ap K₂-map-idf))) ◃∙
      natiso2G-to-== (sq-ΩK idf2G) ◃∙
      idp ◃∎
        =ₛ₁⟨ 2 & 1 & 
          ap ! (! (whisk2G-conv-r (Loop2Grp-map-ap K₂-map-idf))) ∙
          ! (natiso2G-! (natiso-whisk-r (Loop2Grp-map-ap K₂-map-idf))) ⟩
      natiso2G-to-== (unit-wksgrphom-l (grphom-forg K₂-loopmap)) ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-r (Loop2Grp-map-idf ⊙[ K₂ η , base ]))) ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-r (Loop2Grp-map-ap K₂-map-idf))) ◃∙
      natiso2G-to-== (sq-ΩK idf2G) ◃∙
      idp ◃∎
        =ₛ₁⟨ 4 & 1 & ! (natiso2G-to-==-β (K₂-loopmap ∘2G cohgrphom (idf G) {{idf2G}})) ⟩
      natiso2G-to-== (unit-wksgrphom-l (grphom-forg K₂-loopmap)) ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-r (Loop2Grp-map-idf ⊙[ K₂ η , base ]))) ◃∙
      natiso2G-to-== (!ʷ (natiso-whisk-r (Loop2Grp-map-ap K₂-map-idf))) ◃∙
      natiso2G-to-== (sq-ΩK idf2G) ◃∙
      natiso2G-to-== (natiso-id2G (K₂-loopmap ∘2G cohgrphom (idf G) {{idf2G}})) ◃∎
       =ₛ⟨ ∘2G-conv-quint
             (unit-wksgrphom-l (grphom-forg K₂-loopmap))
             (!ʷ (natiso-whisk-r (Loop2Grp-map-idf ⊙[ K₂ η , base ])))
             (!ʷ (natiso-whisk-r (Loop2Grp-map-ap K₂-map-idf)))
             (sq-ΩK idf2G)
             (natiso-id2G (K₂-loopmap ∘2G cohgrphom (idf G) {{idf2G}})) ⟩
     natiso2G-to-==
       (natiso-id2G (K₂-loopmap ∘2G cohgrphom (idf G) {{idf2G}}) natiso-∘
       sq-ΩK idf2G natiso-∘
       !ʷ (natiso-whisk-r (Loop2Grp-map-ap K₂-map-idf)) natiso-∘
       !ʷ (natiso-whisk-r (Loop2Grp-map-idf ⊙[ K₂ η , base ])) natiso-∘
       unit-wksgrphom-l (grphom-forg K₂-loopmap)) ◃∎
       =ₛ₁⟨ ap natiso2G-to-==
              (natiso∼-to-== (λ x →
              aux (ap-idf (loop x)) (WkSGrpNatIso.θ (Loop2Grp-map-ap K₂-map-idf) (loop x)) (K₂-map-β-pts idf2G x) ∙
              =ₛ-out (LoopK-idf {{η}} x))) ⟩
     natiso2G-to-== (unit-wksgrphom-r (grphom-forg K₂-loopmap)) ◃∎ ∎ₛ
       where abstract
         aux : ∀ {j} {A : Type j} {x y z w : A} (p₁ : y == z) (p₂ : x == y) (p₃ : x == w)
           → ((! p₁ ∙ ! p₂) ∙ p₃) ∙ idp == ! (p₂ ∙ p₁) ∙ p₃ ∙ idp
         aux idp idp idp = idp
