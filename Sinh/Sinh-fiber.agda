{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import HoTT
open import lib.types.N-groups
open import lib.types.Torsor
open import homotopy.EilenbergMacLane
open import torsors.Delooping
open import Sinh-classif

{- Consider the cocyle produced by the Sinh-triple for a given n-group BG.
   Its pullback along the basepoint section of the Eilenberg-MacLane type
   family is BG itself. -}

module Sinh-fiber where

module _ {n : ℕ} {i : ULevel} (G@(X , cX , tX) : [ S (S n) , i ]-Groups) where

  open EMExplicit

  private
  
    action : de⊙ (⊙Trunc ⟨ S n ⟩ X) → AbGroup i
    action = fst (snd (NGrp-Sinh–> G))

    cocycle = snd (snd (NGrp-Sinh–> G))
    cocycle-tors = snd (snd (–> NGrp-Sinh-≃-pre G))

  module _ (x : de⊙ (⊙Trunc ⟨ S n ⟩ X)) where
  
    -- the underlying type of the associated torsor is definitionally the fiber of the truncation map
    NGrp-Sinh-coc-tors-fib : fst (fst cocycle-tors x) == hfiber [_] x
    NGrp-Sinh-coc-tors-fib = idp

    abstract
      NGrp-Sinh-coc-tors-fib-≃ :
        (hfiber [_] x)
          ≃
        (fst cocycle-tors x == pt (⊙Torsors (⊙EM (action x) (S (S n))) {{PtdTorsors-contr {{EM-conn (action x)}}}}))
      NGrp-Sinh-coc-tors-fib-≃ =
        tors-ptd-is-trivial (⊙EM (fst (snd (–> NGrp-Sinh-≃-pre G)) x) (S (S n))) {{PtdTorsors-contr {{EM-conn (action x)}}}}

    NGrp-Sinh-coc-fib-≃ :
      (hfiber [_] x)
        ≃
      (fst cocycle x == pt (⊙EM (action x) (S (S (S n)))))
    NGrp-Sinh-coc-fib-≃ = {!!} ∘e NGrp-Sinh-coc-tors-fib-≃
