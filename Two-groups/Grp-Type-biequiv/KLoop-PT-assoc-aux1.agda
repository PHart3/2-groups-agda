{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import LoopK-hom
open import KFunctor-comp
open import KLoop-ptr-comp

module KLoop-PT-assoc-aux1 where

module KL-PT-aux1 {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  {{ηX : has-level 2 (de⊙ X)}} {{ηY : has-level 2 (de⊙ Y)}} {{ηZ : has-level 2 (de⊙ Z)}}
  (f* : X ⊙→ Y) (g* : Y ⊙→ Z) where

  open import KLoop-PT-assoc-defs f* g*

  private
    ç = ⊙→∼-to-== (KLoop-∘ (pt X) (pt Y) (pt Z) f* g*)

  abstract
  
    KLoop-coher-assoc4 : τ₄ =ₛ τ₅
    KLoop-coher-assoc4 = =ₛ-in (ap ⊙-crd∼-to-== ç)

    KLoop-coher-assoc5 :
      τ₅
        =ₛ
      idp {a = K₂-rec-hom (pt Z) (idf2G {{Loop2Grp (pt Z)}}) ⊙∘ K₂-action-hom (Loop2Grp-map (g* ⊙∘ f*))} ◃∎
    KLoop-coher-assoc5 = =ₛ-in (⊙-crd∼-to-==-β (K₂-rec-hom (pt Z) (idf2G {{Loop2Grp (pt Z)}}) ⊙∘ K₂-action-hom (Loop2Grp-map (g* ⊙∘ f*))))
