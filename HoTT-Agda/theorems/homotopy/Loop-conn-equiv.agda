{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.NConnected
open import lib.Function2
open import lib.types.LoopSpace
open import lib.types.Pi
open import lib.Equivalence2
open import lib.types.Truncation
open import lib.types.TLevel

module homotopy.Loop-conn-equiv where

module _ {i j} {X : Ptd i} {Y : Ptd j} {{cX : is-connected 0 (de⊙ X)}} {{cY : is-connected 0 (de⊙ Y)}} where

  abstract
    -- If f is a map of pointed connected types and Ω f is an equivalence, then so is f.
    Ω-conn-≃ : (f* : X ⊙→ Y) → is-equiv (Ω-fmap f*) → is-equiv (fst f*)
    Ω-conn-≃ (f , idp) eΩ = surj-emb-is-equiv (emb , surj)
      -- f is a surjective embedding.
      where
      
        emb : is-embedding f
        emb = prop-over-connected
          (λ z → ((y : de⊙ X) → is-equiv (of-type (z == y → f z == f y) (ap f))) , ⟨⟩)
          (prop-over-connected (λ z → is-equiv (of-type (_ == z → f _ == f z) (ap f)) , ⟨⟩) eΩ)

        surj : is-surj f
        surj = prop-over-connected (λ z → Trunc -1 (hfiber f z) , ⟨⟩) [ (pt X) , idp ]

abstract
  -- If f is a map of pointed n-connected types and Ω^(n + ) f is an equivalence, then so is f.
  Ω-Nconn-≃ : ∀ {i j} {X : Ptd i} {Y : Ptd j}
    {n : ℕ} {{cX : is-connected (tl n) (de⊙ X)}} {{cY : is-connected (tl n) (de⊙ Y)}} (f* : X ⊙→ Y)
    → is-equiv (Ω^'-fmap (S n) f*) → is-equiv (fst f*)
  Ω-Nconn-≃ {n = O} = Ω-conn-≃
  Ω-Nconn-≃ {n = S n} {{cX}} {{cY}} f* ise =
    Ω-conn-≃ {{connected-≤T tl-S-≤T}} {{connected-≤T tl-S-≤T}} f* (Ω-Nconn-≃ {n = n} (⊙Ω-fmap f*) ise) 
