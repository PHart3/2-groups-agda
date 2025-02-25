{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import K-hom-ind
open import KFunctor
open import Delooping
open import LoopK
open import KFunctor-comp
open import SqKLoop
open import apK-aux2

module KLoop-ptr-comp-aux0 where

module _ {i j k} {X : Type i} {Y : Type j} {Z : Type k}
  {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {{ηZ : has-level 2 Z}}
  (f : X → Y) (g : Y → Z) (x₀ : X) (x : x₀ == x₀) where

  private
    y₀ = f x₀
    z₀ = g (f x₀) {-
    Λx₀ = wkmag-to-loop x₀ (cohmaghom (idf (x₀ == x₀)) {{idf2G}})
    Λy₀ = wkmag-to-loop y₀ (cohmaghom (idf (y₀ == y₀)) {{idf2G}})
    Λz₀ = wkmag-to-loop z₀ (cohmaghom (idf (z₀ == z₀)) {{idf2G}})
    K₂-rec-x₀ = K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)
    K₂-rec-y₀ = K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)
    K₂-rec-z₀ = K₂-rec (z₀ == z₀) z₀ (loop' Λz₀) (loop-comp' Λz₀) (loop-assoc' Λz₀) -}

  abstract
    KLoop-∘-coher : (α₁ : _) (α₂ : _) (α₃ : _) (α₄ : _) →
      hmpty-nat-∙'
        (λ x₁ →
          ! (K₂-∼-ind
              (g ∘ f ∘ K₂-rec-x₀ x₀ z₀)
              (K₂-rec-y₀ x₀ z₀ ∘ K₂-map (Loop2Grp-map-str (g ∘ f , idp)))
              idp
              (λ x₂ →
                ap-∘ (g ∘ f) (K₂-rec-x₀ x₀ z₀) (loop (x₀ == x₀) x₂) ∙
                ap (ap (g ∘ f)) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x₂) ∙
                ! (K₂-rec-hom-β-pts z₀ (idf2G {{Loop2Grp z₀}}) (ap (g ∘ f) x₂)) ∙
                ! (ap (ap (K₂-rec-y₀ x₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g ∘ f , idp)) x₂)) ∙
                ! (ap-∘ (K₂-rec-y₀ x₀ z₀) (K₂-map (Loop2Grp-map-str (g ∘ f , idp))) (loop (x₀ == x₀) x₂)))
              α₁ x₁) ∙
            ap g
              (K₂-∼-ind
                (f ∘ K₂-rec-x₀ x₀ y₀)
                (K₂-rec-y₀ x₀ y₀ ∘ K₂-map (Loop2Grp-map-str (f , idp)))
                idp
                (λ x₂ →
                  ap-∘ f (K₂-rec-x₀ x₀ y₀) (loop (x₀ == x₀) x₂) ∙
                  ap (ap f) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) x₂) ∙
                  ! (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f x₂)) ∙
                  ! (ap (ap (K₂-rec-y₀ x₀ y₀)) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x₂)) ∙
                  ! (ap-∘ (K₂-rec-y₀ x₀ y₀) (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) x₂)))
                α₂ x₁) ∙
            K₂-∼-ind
              (g ∘ K₂-rec-x₀ y₀ z₀)
              (K₂-rec-y₀ y₀ z₀ ∘ K₂-map (Loop2Grp-map-str (g , idp)))
              idp
              (λ x₂ →
                ap-∘ g (K₂-rec-x₀ y₀ z₀) (loop (y₀ == y₀) x₂) ∙
                ap (ap g) (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) x₂) ∙
                ! (K₂-rec-hom-β-pts z₀ (idf2G {{Loop2Grp z₀}}) (ap g x₂)) ∙
                ! (ap (ap (K₂-rec-y₀ y₀ z₀)) (K₂-map-β-pts (Loop2Grp-map-str (g , idp)) x₂)) ∙
                ! (ap-∘ (K₂-rec-y₀ y₀ z₀) (K₂-map (Loop2Grp-map-str (g , idp))) (loop (y₀ == y₀) x₂)))
              α₃ (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp))) x₁) ∙
            ! (ap (fst (K₂-rec-hom z₀ idf2G))
                (K₂-∼-ind
                  (fst (K₂-map⊙ (Loop2Grp-map-str (g ∘ f , idp))))
                  (fst (K₂-map⊙ (cohmaghom (ap g) {{Loop2Grp-map-str (g , idp)}} ∘2Mσ cohmaghom (ap f) {{Loop2Grp-map-str (f , idp)}})))
                  idp
                  (λ x₂ →
                    K₂-map-β-pts (Loop2Grp-map-str (g ∘ f , idp)) x₂ ∙
                    ap (loop (z₀ == z₀)) (ap-∘ g f x₂) ∙
                    ! (K₂-map-β-pts (cohmaghom (ap g) {{Loop2Grp-map-str (g , idp)}} ∘2Mσ cohmaghom (ap f) {{Loop2Grp-map-str (f , idp)}}) x₂))
                  (apK₂-coher (Loop2Grp-map-∘ (g , idp) (f , idp))) x₁ ∙
                K₂-∼-ind
                  (map₁-∘ (Loop2Grp-map-str (f , idp)) (Loop2Grp-map-str (g , idp)))
                  (map₂-∘ (Loop2Grp-map-str (f , idp)) (Loop2Grp-map-str (g , idp)))
                  idp
                  (λ x₂ →
                    K₂-map-β-pts (cohgrphom (ap g) {{Loop2Grp-map-str (g , idp)}} ∘2Gσ cohgrphom (ap f) {{Loop2Grp-map-str (f , idp)}}) x₂ ∙
                    ! (K₂-map-β-pts (Loop2Grp-map-str (g , idp)) (ap f x₂)) ∙
                    ! (ap (ap (K₂-map (Loop2Grp-map-str (g , idp)))) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) x₂)) ∙
                    ∘-ap (K₂-map (Loop2Grp-map-str (g , idp))) (K₂-map (Loop2Grp-map-str (f , idp))) (loop (x₀ == x₀) x₂))
                  α₄ x₁)))
        (loop (x₀ == x₀) x)
        ==
      hmpty-nat-∙' (λ x₁ → idp) (loop (x₀ == x₀) x)
    KLoop-∘-coher = ?

{-
  α₁ = (Sq-aux10.SqKLoop-coher x₀ (g ∘ f))
  α₂ = (Sq-aux10.SqKLoop-coher x₀ f)
  α₃ = (Sq-aux10.SqKLoop-coher y₀ g)
  α₄ = (K₂-map-∘-aux.K₂-map-∘-coher (Loop2Grp-map-str (f , idp)) (Loop2Grp-map-str (g , idp)))
-}
