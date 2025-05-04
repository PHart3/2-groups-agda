{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NConnected
open import lib.Surjection
open import lib.types.LoopSpace
open import lib.types.Pi
open import lib.Equivalence2
open import lib.types.Truncation

module homotopy.Loop-conn-equiv where

module _ {i j} {X : Ptd i} {Y : Ptd j} {{cX : is-connected 0 (de⊙ X)}} {{cY : is-connected 0 (de⊙ Y)}} where

  abstract
    Ω-conn-≃ : (f* : X ⊙→ Y) → is-equiv (Ω-fmap f*) → is-equiv (fst f*)
    Ω-conn-≃ (f , idp) eΩ = surj-emb-is-equiv (emb , surj)
      where
        emb : is-embedding f
        emb = prop-over-connected
          (λ z → ((y : de⊙ X) → is-equiv (of-type (z == y → f z == f y) (ap f))) , ⟨⟩)
          (prop-over-connected (λ z → is-equiv (of-type (_ == z → f _ == f z) (ap f)) , ⟨⟩) eΩ)

        surj : is-surj f
        surj = prop-over-connected (λ z → Trunc -1 (hfiber f z) , ⟨⟩) [ (pt X) , idp ]
