{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed

module lib.wild-cats.Ptd-wc where

open import lib.wild-cats.WildCat public
open import lib.wild-cats.WildFunctor public

Ptd-wc : (i : ULevel) → WildCat
ob (Ptd-wc i) = Ptd i
hom (Ptd-wc _) X Y = X ⊙→ Y
id₁ (Ptd-wc _) X = ⊙idf X
_▢_ (Ptd-wc _) g f = g ⊙∘ f
ρ (Ptd-wc _) f = ⊙-comp-to-== (⊙∘-runit f) 
lamb (Ptd-wc _) f = ⊙-comp-to-== (⊙∘-lunit f)
α (Ptd-wc _) h g f = ⊙-comp-to-== (⊙∘-assoc-comp h g f)

PtdFunctor : (i j : ULevel) → Type (lsucc (lmax i j))
PtdFunctor i j = Functor-wc (Ptd-wc i) (Ptd-wc j)

module _ {i} {X Y : Ptd i} where

  ⊙≃-to-equiv-wc : (e : X ⊙≃ Y) → equiv-wc (Ptd-wc i) (fst e)
  fst (⊙≃-to-equiv-wc e) = ⊙<– e
  fst (snd (⊙≃-to-equiv-wc e)) = ! (⊙λ= (⊙<–-inv-l e))
  snd (snd (⊙≃-to-equiv-wc e)) = ! (⊙λ= (⊙<–-inv-r e))

  ⊙≃-from-equiv-wc : {f : X ⊙→ Y} → equiv-wc (Ptd-wc i) f → X ⊙≃ Y
  fst (⊙≃-from-equiv-wc {f} e) = f
  snd (⊙≃-from-equiv-wc {f} e) = is-eq (fst f) (fst (<–-wc (Ptd-wc _) e))
    (λ x → ! (fst (⊙app= (<–-wc-rinv (Ptd-wc _) e)) x))
    λ x → ! (fst (⊙app= (<–-wc-linv (Ptd-wc _) e)) x)
