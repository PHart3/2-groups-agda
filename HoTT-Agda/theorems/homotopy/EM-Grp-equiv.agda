{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import HoTT
open import homotopy.HSpace renaming (HSpaceStructure to HSS)
open import homotopy.Freudenthal
open import homotopy.IterSuspensionStable
import homotopy.Pi2HSusp as Pi2HSusp
open import homotopy.EM1HSpace
open import homotopy.EilenbergMacLane1
open import homotopy.EilenbergMacLane
open import homotopy.SuspAdjointLoop

-- equivalence between set-level groups and pointed n-connected, (n+1)-types

module homotopy.EM-Grp-equiv {i} (G : AbGroup i) where

open AbGroup G
open EMExplicit

-- recursion principle for K(G, n)
⊙EM-elimₙ : (n : ℕ) {j : ULevel} {X : Ptd j} {{X-level : has-level ⟨ S n ⟩ (de⊙ X)}}
  → (grp →ᴳ Ω^'S-group n X) → ⊙EM G (S n) ⊙→ X
⊙EM-elimₙ O {X = X@(⊙[ X₀ , pt ])} φ = (f ∘ –> (unTrunc-equiv (EM₁ (fst G)) {{EM₁-level₁ grp}})) , idp where open EM₁Level₁Rec pt φ
⊙EM-elimₙ (S n) {X = X} φ = ⊙Trunc-rec (ε X ⊙∘ ⊙Susp-fmap (⊙EM-elimₙ n {X = ⊙Ω X} φ ⊙∘ [_]-⊙))
