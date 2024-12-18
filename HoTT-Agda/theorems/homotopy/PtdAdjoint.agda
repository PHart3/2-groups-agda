{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed

{- The pseudo-adjoint functors F,G : Ptd → Ptd
 - It stops at composition and ignores
 - all the higher associahedrons.
 -}

module homotopy.PtdAdjoint where

record PtdFunctor i j : Type (lsucc (lmax i j)) where
  field
    obj : Ptd i → Ptd j
    arr : {X Y : Ptd i} → X ⊙→ Y → obj X ⊙→ obj Y
    id : (X : Ptd i) → arr (⊙idf X) == ⊙idf (obj X)
    comp : {X Y Z : Ptd i} (g : Y ⊙→ Z) (f : X ⊙→ Y)
      → arr (g ⊙∘ f) == arr g ⊙∘ arr f

{- counit-unit description of F ⊣ G -}
record CounitUnitAdjoint {i j} (F : PtdFunctor i j) (G : PtdFunctor j i)
  : Type (lsucc (lmax i j)) where

  private
    module F = PtdFunctor F
    module G = PtdFunctor G

  field
    η : (X : Ptd i) → (X ⊙→ G.obj (F.obj X))
    ε : (U : Ptd j) → (F.obj (G.obj U) ⊙→ U)

    η-natural : {X Y : Ptd i} (h : X ⊙→ Y)
      → η Y ⊙∘ h == G.arr (F.arr h) ⊙∘ η X
    ε-natural : {U V : Ptd j} (k : U ⊙→ V)
      → ε V ⊙∘ F.arr (G.arr k) == k ⊙∘ ε U

    εF-Fη : (X : Ptd i) → ε (F.obj X) ⊙∘ F.arr (η X) == ⊙idf (F.obj X)
    Gε-ηG : (U : Ptd j) → G.arr (ε U) ⊙∘ η (G.obj U) == ⊙idf (G.obj U)

{- hom-set isomorphism description of F ⊣ G -}
record HomAdjoint {i j} (F : PtdFunctor i j) (G : PtdFunctor j i)
  : Type (lsucc (lmax i j)) where

  private
    module F = PtdFunctor F
    module G = PtdFunctor G

  field
    eq : (X : Ptd i) (U : Ptd j) → (F.obj X ⊙→ U) ≃ (X ⊙→ G.obj U)

    nat-dom : {X Y : Ptd i} (h : X ⊙→ Y) (U : Ptd j)
      (r : F.obj Y ⊙→ U)
      → –> (eq Y U) r ⊙∘ h == –> (eq X U) (r ⊙∘ F.arr h)

    nat-cod : (X : Ptd i) {U V : Ptd j} (k : U ⊙→ V)
      (r : F.obj X ⊙→ U)
      → G.arr k ⊙∘ –> (eq X U) r == –> (eq X V) (k ⊙∘ r)

  nat!-dom : {X Y : Ptd i} (h : X ⊙→ Y) (U : Ptd j)
    (s : Y ⊙→ G.obj U)
    → <– (eq Y U) s ⊙∘ F.arr h == <– (eq X U) (s ⊙∘ h)
  nat!-dom {X} {Y} h U s =
    ! (<–-inv-l (eq X U) (<– (eq Y U) s ⊙∘ F.arr h))
    ∙ ap (<– (eq X U)) (! (nat-dom h U (<– (eq Y U) s)))
    ∙ ap (λ w → <– (eq X U) (w ⊙∘ h)) (<–-inv-r (eq Y U) s)

  nat!-cod : (X : Ptd i) {U V : Ptd j} (k : U ⊙→ V)
    (s : X ⊙→ G.obj U)
    → k ⊙∘ <– (eq X U) s == <– (eq X V) (G.arr k ⊙∘ s)
  nat!-cod X {U} {V} k s =
    ! (<–-inv-l (eq X V) (k ⊙∘ <– (eq X U) s))
    ∙ ap (<– (eq X V)) (! (nat-cod X k (<– (eq X U) s)))
    ∙ ap (λ w → <– (eq X V) (G.arr k ⊙∘ w)) (<–-inv-r (eq X U) s)
