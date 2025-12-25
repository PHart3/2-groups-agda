{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import 2Grp-bc
open import Ptd-bc
open import AdjEqv-exmps
open import Biequiv
open import Biequiv-main
open import Biadj-data.Loop-zig-zag

-- Final theorem: biadjoint biequivalence between 2-groups and pointed connected 2-types

module Biadj-biequiv-main where
  
  import Biadj
  open Biadj.Biequiv-coh
  import Pstransf-SIP
  open Pstransf-SIP.InvMod

  2Grp-Ptd02-baeq : ∀ i → (Ptd02-bicat i) biadj-bieqv (2grp-bicat i)
  fst (2Grp-Ptd02-baeq i) = 2Grp-Ptd02-bieq i
  η₀-∼ (ζζ (snd (2Grp-Ptd02-baeq i))) (X , _ , tr) = Loop-zz₀ {{tr}} (pt X)
  η₁-∼ (ζζ (snd (2Grp-Ptd02-baeq i))) {X₁ , _ , tr₁} {X₂ , _ , tr₂} f = =ₛ-out (Loop-zz₁ {{tr₁}} {{tr₂}} f)
