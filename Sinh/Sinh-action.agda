{-# OPTIONS --without-K --rewriting --overlapping-instances --lossy-unification #-}

open import HoTT
open import lib.types.N-groups
open import Sinh-classif

{- The action produced by the Sinh-triple for a given higher group
   is the canonical action of πₙ₊₁ on πₙ₊₂ (where n ≥ 0). -}

module Sinh-action where

module _ {n : ℕ} {i : ULevel} (G@(X , cX , tX) : [ S (S n) , i ]-Groups) where

  NGrp-Sinh–> : [ S (S n) , i ]-Groups → Sinh-triples (S n) i
  NGrp-Sinh–> = –> NGrp-Sinh-≃

  NGrp-Sinh-≃-group : fst (fst (NGrp-Sinh–> G)) == ⊙Trunc ⟨ S n ⟩ X
  NGrp-Sinh-≃-group = idp

  πₙ-can-action : de⊙ (⊙Trunc ⟨ S n ⟩ X) → AbGroup i
  πₙ-can-action = Trunc-rec {{grpd-has-level-SSS ⟨⟩}} (λ u → Ω^'S-abgroup n ⊙[ de⊙ X , u ] {{tX}})

  NGrp-Sinh-≃-action-aux : ∀ {u} y →
    Ω^'S-abgroup n (⊙[ hfiber [_] u , y ]) {{Σ-level tX λ _ → =-preserves-level (raise-level _ ⟨⟩)}}
      ==
    fst (snd (NGrp-Sinh–> G)) u
  NGrp-Sinh-≃-action-aux {u} y = snd (snd (snd (fst (snd (snd (snd
    (–> (Sinh-classif-lemmas.rearrange ∘e Sinh-classif-lemmas.orthog-contr ∘e N-Grps-≃) G)))) u))) y

  NGrp-Sinh-≃-action : fst (snd (NGrp-Sinh–> G)) ∼ πₙ-can-action
  NGrp-Sinh-≃-action = Trunc-elim {{has-level-apply-instance {{grpd-has-level-SSS ⟨⟩}}}} λ u →
    ! (NGrp-Sinh-≃-action-aux (u , idp)) ∙
    uaᴳ-Ab (group-hom map (Ω^'-hfib-Trunc-∙ {{tX}}) , snd (Ω^'-hfib-Trunc (S n) {{tX}}))
      where
        map : {u : de⊙ (fst G)}
          → Ω^' (S (S n)) ⊙[ hfiber [_] [ u ] , (u , idp) ] → Ω^' (S (S n)) ⊙[ de⊙ (fst G) , u ]
        map {u} = –> (Ω^'-hfib-Trunc (S n) {x = u} {{tX}})
