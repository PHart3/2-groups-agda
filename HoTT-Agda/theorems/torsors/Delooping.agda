{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.FTID
open import lib.NConnected
open import lib.types.LoopSpace
open import lib.types.Truncation
open import lib.types.Torsor
open import lib.types.Pi
open import lib.types.Paths
open import lib.types.TLevel
open import homotopy.Loop-conn-equiv

-- The type of torsors over a pointed type X as the delooping of X

module torsors.Delooping where

module _ {i j : ULevel} (X : Ptd i) {{c : is-contr (PtdTorsors j X)}} where

  private
    R = contr-center c
    R₀ = fst R
    r₀ = snd R

  ⊙Torsors : Ptd (lmax i (lsucc j))
  ⊙Torsors = ⊙[ Torsors j X , R₀ ]

  tors-ptd-is-trivial : {Q : Torsors j X} → fst Q ≃ (Q == R₀)
  tors-ptd-is-trivial {Q} = id-sys-==

  abstract
    Torsors-conn : is-connected 0 (Torsors j X)
    Torsors-conn = path-conn-conn [ R₀ ] (uncurry λ Z → uncurry (Trunc-elim λ z μ → uncurry λ W → uncurry
      (Trunc-elim λ w ν → [ –> tors-ptd-is-trivial z ∙ ! (–> tors-ptd-is-trivial w) ])))

  ⊙tors-ptd-is-trivial : ⊙[ (fst R₀) , r₀ ] ⊙≃ ⊙Ω ⊙Torsors
  fst ⊙tors-ptd-is-trivial = (fst tors-ptd-is-trivial) , id-sys-==-map-β
  snd ⊙tors-ptd-is-trivial = snd tors-ptd-is-trivial

  tors-is-delooping : X ⊙≃ ⊙Ω ⊙Torsors
  tors-is-delooping = ⊙tors-ptd-is-trivial ⊙∘e Torsor-pr22 R₀ r₀

  module _ {Z*@(⊙[ Z , z₀ ]) : Ptd j} {{cZ : is-connected 0 Z}} (d : X ⊙≃ ⊙Ω Z*) where

    tors-uniq-map : Z → Torsors j X
    fst (tors-uniq-map z) = z == z₀
    fst (snd (tors-uniq-map z)) = prop-over-connected (λ z → Trunc -1 (z == z₀) , ⟨⟩) [ idp ] z
    snd (snd (tors-uniq-map z)) idp = d

    ⊙tors-uniq-map : Z* ⊙→ ⊙Torsors
    fst ⊙tors-uniq-map = tors-uniq-map
    snd ⊙tors-uniq-map = –> tors-ptd-is-trivial idp

    Ω-tors-uniq-map-β : (p : z₀ == z₀) →
      Ω-fmap (⊙tors-uniq-map) p == ! (–> (tors-ptd-is-trivial {tors-uniq-map z₀}) idp) ∙ –> tors-ptd-is-trivial p
    Ω-tors-uniq-map-β p = Ω-fmap-β (⊙tors-uniq-map) p ∙ ap (λ q → ! (–> tors-ptd-is-trivial idp) ∙ q) (aux z₀ p)
      where
        aux : (z : Z) → (q : z == z₀) → ap tors-uniq-map q ∙' –> tors-ptd-is-trivial idp == –> tors-ptd-is-trivial q
        aux z idp = ∙'-unit-l _

    ⊙Ω-tors-uniq-map-eqv : is-equiv (Ω-fmap (⊙tors-uniq-map))
    ⊙Ω-tors-uniq-map-eqv = ∼-preserves-equiv (! ∘ Ω-tors-uniq-map-β)
      (pre∙-is-equiv (! (–> (tors-ptd-is-trivial {tors-uniq-map z₀}) idp)) ∘ise snd tors-ptd-is-trivial)

    ⊙tors-uniq-map-≃ : Z* ⊙≃ ⊙Torsors
    fst ⊙tors-uniq-map-≃ = ⊙tors-uniq-map
    snd ⊙tors-uniq-map-≃ = Ω-conn-≃ {{cY = Torsors-conn}} ⊙tors-uniq-map ⊙Ω-tors-uniq-map-eqv
