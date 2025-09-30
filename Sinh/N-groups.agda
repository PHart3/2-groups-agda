{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.FTID
open import lib.NConnected
open import lib.types.Sigma
open import lib.types.TLevel
open import lib.types.Truncation

-- two equivalent ways of describing n-groups as synthetic higher groups

module N-groups where

[_,_]-Groups : (n : ℕ) (i : ULevel) → Type (lsucc i)
[ n , i ]-Groups = Σ (Ptd i) (λ X → is-connected 0 (de⊙ X) × has-level ⟨ n ⟩ (de⊙ X))

[_,_]-conn-trunc : (n : ℕ) (i : ULevel) → Type (lsucc i)
[ n , i ]-conn-trunc = Σ (Type i) (λ X → is-connected ⟨ n ⟩ X × has-level ⟨ S n ⟩ X)

[_,_,_]-Groups-v2 : (n : ℕ) (i j : ULevel) → Type (lmax (lsucc i) (lsucc j))
[ n , i , j ]-Groups-v2 = [ BG ∈ [ n , i ]-Groups ] × [ F ∈ (de⊙ (fst BG) →  [ n , j ]-conn-trunc) ] × fst (F (pt (fst BG)))

