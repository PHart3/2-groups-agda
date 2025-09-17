{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import lib.wild-cats.Ptd-wc

{- The pseudo-adjoint functors F,G : Ptd → Ptd
 - It stops at composition and ignores
 - all the higher associahedrons.
 -}

module homotopy.PtdAdjoint where

{- counit-unit description of F ⊣ G -}
record CounitUnitAdjoint {i j} (F : PtdFunctor i j) (G : PtdFunctor j i)
  : Type (lsucc (lmax i j)) where

  field
    η : (X : Ptd i) → (X ⊙→ obj G (obj F X))
    ε : (U : Ptd j) → (obj F (obj G U) ⊙→ U)

    η-natural : {X Y : Ptd i} (h : X ⊙→ Y)
      → η Y ⊙∘ h == arr G (arr F h) ⊙∘ η X
    ε-natural : {U V : Ptd j} (k : U ⊙→ V)
      → ε V ⊙∘ arr F (arr G k) == k ⊙∘ ε U

    εF-Fη : (X : Ptd i) → ε (obj F X) ⊙∘ arr F (η X) == ⊙idf (obj F X)
    Gε-ηG : (U : Ptd j) → arr G (ε U) ⊙∘ η (obj G U) == ⊙idf (obj G U)

  F-Gε-ηG : ∀ {k} (K : PtdFunctor i k) (U : Ptd j) → arr K (arr G (ε U)) ⊙∘ arr K (η (obj G U)) == ⊙idf (obj K (obj G U))
  F-Gε-ηG K U = ! (comp K (η (obj G U)) (arr G (ε U))) ∙ ap (arr K) (Gε-ηG U) ∙ id K (obj G U)

{- hom-set isomorphism description of F ⊣ G -}
record HomAdjoint {i j} (F : PtdFunctor i j) (G : PtdFunctor j i)
  : Type (lsucc (lmax i j)) where

  field
    eq : (X : Ptd i) (U : Ptd j) → (obj F X ⊙→ U) ≃ (X ⊙→ obj G U)

    nat-dom : {X Y : Ptd i} (h : X ⊙→ Y) (U : Ptd j)
      (r : obj F Y ⊙→ U)
      → –> (eq Y U) r ⊙∘ h == –> (eq X U) (r ⊙∘ arr F h)

    nat-cod : (X : Ptd i) {U V : Ptd j} (k : U ⊙→ V)
      (r : obj F X ⊙→ U)
      → arr G k ⊙∘ –> (eq X U) r == –> (eq X V) (k ⊙∘ r)

  nat!-dom : {X Y : Ptd i} (h : X ⊙→ Y) (U : Ptd j)
    (s : Y ⊙→ obj G U)
    → <– (eq Y U) s ⊙∘ arr F h == <– (eq X U) (s ⊙∘ h)
  nat!-dom {X} {Y} h U s =
    ! (<–-inv-l (eq X U) (<– (eq Y U) s ⊙∘ arr F h))
    ∙ ap (<– (eq X U)) (! (nat-dom h U (<– (eq Y U) s)))
    ∙ ap (λ w → <– (eq X U) (w ⊙∘ h)) (<–-inv-r (eq Y U) s)

  nat!-cod : (X : Ptd i) {U V : Ptd j} (k : U ⊙→ V)
    (s : X ⊙→ obj G U)
    → k ⊙∘ <– (eq X U) s == <– (eq X V) (arr G k ⊙∘ s)
  nat!-cod X {U} {V} k s =
    ! (<–-inv-l (eq X V) (k ⊙∘ <– (eq X U) s))
    ∙ ap (<– (eq X V)) (! (nat-cod X k (<– (eq X U) s)))
    ∙ ap (λ w → <– (eq X V) (arr G k ⊙∘ w)) (<–-inv-r (eq X U) s)

counit-unit-to-hom : ∀ {i j} {F : PtdFunctor i j} {G : PtdFunctor j i}
  → CounitUnitAdjoint F G → HomAdjoint F G
counit-unit-to-hom {i} {j} {F} {G} adj = record {
  eq = eq;
  nat-dom = nat-dom;
  nat-cod = nat-cod}
  where
  open CounitUnitAdjoint adj

  module _ (X : Ptd i) (U : Ptd j) where

    into : obj F X ⊙→ U → X ⊙→ obj G U
    into r = arr G r ⊙∘ η X

    out : X ⊙→ obj G U → obj F X ⊙→ U
    out s = ε U ⊙∘ arr F s

    into-out : (s : X ⊙→ obj G U) → into (out s) == s
    into-out s =
      arr G (ε U ⊙∘ arr F s) ⊙∘ η X
        =⟨ comp G (arr F s)(ε U) |in-ctx (λ w → w ⊙∘ η X) ⟩
      (arr G (ε U) ⊙∘ arr G (arr F s)) ⊙∘ η X
        =⟨ ⊙λ= $ ⊙∘-assoc (arr G (ε U)) (arr G (arr F s)) (η X) ⟩
      arr G (ε U) ⊙∘ arr G (arr F s) ⊙∘ η X
        =⟨ ! (η-natural s) |in-ctx (λ w → arr G (ε U) ⊙∘ w) ⟩
      arr G (ε U) ⊙∘ η (obj G U) ⊙∘ s
        =⟨ ! $ ⊙λ= (⊙∘-assoc (arr G (ε U)) (η (obj G U)) s) ⟩
      (arr G (ε U) ⊙∘ η (obj G U)) ⊙∘ s
        =⟨ Gε-ηG U |in-ctx (λ w → w ⊙∘ s) ⟩
      ⊙idf (obj G U) ⊙∘ s
        =⟨ ⊙λ= $ ⊙∘-unit-l s ⟩
      s =∎

    out-into : (r : obj F X ⊙→ U) → out (into r) == r
    out-into r =
      ε U ⊙∘ arr F (arr G r ⊙∘ η X)
        =⟨ comp F (η X) (arr G r) |in-ctx (λ w → ε U ⊙∘ w) ⟩
      ε U ⊙∘ arr F (arr G r) ⊙∘ arr F (η X)
        =⟨ ! $ ⊙λ= (⊙∘-assoc (ε U) (arr F (arr G r)) (arr F (η X))) ⟩
      (ε U ⊙∘ arr F (arr G r)) ⊙∘ arr F (η X)
        =⟨ ε-natural r |in-ctx (λ w → w ⊙∘ arr F (η X)) ⟩
      (r ⊙∘ ε (obj F X)) ⊙∘ arr F (η X)
        =⟨ ⊙λ= $ ⊙∘-assoc r (ε (obj F X)) (arr F (η X)) ⟩
      r ⊙∘ ε (obj F X) ⊙∘ arr F (η X)
        =⟨ εF-Fη X |in-ctx (λ w → r ⊙∘ w) ⟩
      r =∎

    eq : (obj F X ⊙→ U) ≃ (X ⊙→ obj G U)
    eq = equiv into out into-out out-into

  nat-dom : {X Y : Ptd i} (h : X ⊙→ Y) (U : Ptd j)
    (r : obj F Y ⊙→ U)
    → –> (eq Y U) r ⊙∘ h == –> (eq X U) (r ⊙∘ arr F h)
  nat-dom {X} {Y} h U r =
    (arr G r ⊙∘ η Y) ⊙∘ h
      =⟨ ⊙λ= $ ⊙∘-assoc (arr G r) (η Y) h ⟩
    arr G r ⊙∘ η Y ⊙∘ h
      =⟨ η-natural h |in-ctx (λ w → arr G r ⊙∘ w) ⟩
    arr G r ⊙∘ arr G (arr F h) ⊙∘ η X
      =⟨ ! $ ⊙λ= (⊙∘-assoc (arr G r) (arr G (arr F h)) (η X)) ⟩
    (arr G r ⊙∘ arr G (arr F h)) ⊙∘ η X
      =⟨ ! (comp G (arr F h) r) |in-ctx (λ w → w ⊙∘ η X) ⟩
    arr G (r ⊙∘ arr F h) ⊙∘ η X =∎

  nat-cod : (X : Ptd i) {U V : Ptd j} (k : U ⊙→ V)
    (r : obj F X ⊙→ U)
    → arr G k ⊙∘ –> (eq X U) r == –> (eq X V) (k ⊙∘ r)
  nat-cod X k r =
    arr G k ⊙∘ (arr G r ⊙∘ η X)
      =⟨ ! $ ⊙λ= (⊙∘-assoc (arr G k) (arr G r) (η X)) ⟩
    (arr G k ⊙∘ arr G r) ⊙∘ η X
      =⟨ ! (comp G r k) |in-ctx (λ w → w ⊙∘ η X) ⟩
    arr G (k ⊙∘ r) ⊙∘ η X =∎

{- a right adjoint preserves products -}
module RightAdjoint× {i j} {F : PtdFunctor i j} {G : PtdFunctor j i}
  (adj : HomAdjoint F G) (U V : Ptd j) where

  private
    module A = HomAdjoint adj

  ⊙into : obj G (U ⊙× V) ⊙→ obj G U ⊙× obj G V
  ⊙into = ⊙fanout (arr G ⊙fst) (arr G ⊙snd)

  ⊙out : obj G U ⊙× obj G V ⊙→ obj G (U ⊙× V)
  ⊙out = –> (A.eq (obj G U ⊙× obj G V) (U ⊙× V)) (⊙fanout (<– (A.eq (obj G U ⊙× obj G V) U) ⊙fst)
                                                          (<– (A.eq (obj G U ⊙× obj G V) V) ⊙snd))

  ⊙into-out : ⊙into ⊙∘ ⊙out == ⊙idf (obj G U ⊙× obj G V)
  ⊙into-out =
    ⊙fanout (arr G ⊙fst) (arr G ⊙snd) ⊙∘ ⊙out
      =⟨ ⊙fanout-pre∘ (arr G ⊙fst) (arr G ⊙snd) ⊙out ⟩
    ⊙fanout (arr G ⊙fst ⊙∘ ⊙out) (arr G ⊙snd ⊙∘ ⊙out)
      =⟨ ap2 ⊙fanout
           (A.nat-cod _ ⊙fst (⊙fanout (<– (A.eq (obj G U ⊙× obj G V) U) ⊙fst) (<– (A.eq (obj G U ⊙× obj G V) V) ⊙snd))
            ∙ ap (–> (A.eq (obj G U ⊙× obj G V) U))
                 (⊙fst-fanout (<– (A.eq (obj G U ⊙× obj G V) U) ⊙fst) (<– (A.eq (obj G U ⊙× obj G V) V) ⊙snd))
            ∙ <–-inv-r (A.eq (obj G U ⊙× obj G V) U) ⊙fst)
           (A.nat-cod _ ⊙snd (⊙fanout (<– (A.eq (obj G U ⊙× obj G V) U) ⊙fst) (<– (A.eq (obj G U ⊙× obj G V) V) ⊙snd))
            ∙ ap (–> (A.eq (obj G U ⊙× obj G V) V))
                 (⊙snd-fanout (<– (A.eq (obj G U ⊙× obj G V) U) ⊙fst) (<– (A.eq (obj G U ⊙× obj G V) V) ⊙snd))
            ∙ <–-inv-r (A.eq (obj G U ⊙× obj G V) V) ⊙snd) ⟩
    ⊙fanout ⊙fst ⊙snd =∎

  ⊙out-into : ⊙out ⊙∘ ⊙into == ⊙idf _
  ⊙out-into =
    –> (A.eq (obj G U ⊙× obj G V) (U ⊙× V)) (⊙fanout (<– (A.eq (obj G U ⊙× obj G V) U) ⊙fst) (<– (A.eq (obj G U ⊙× obj G V) V) ⊙snd))
    ⊙∘ ⊙fanout (arr G ⊙fst) (arr G ⊙snd)
      =⟨ A.nat-dom (⊙fanout (arr G ⊙fst) (arr G ⊙snd)) _
           (⊙fanout (<– (A.eq (obj G U ⊙× obj G V) U) ⊙fst) (<– (A.eq (obj G U ⊙× obj G V) V) ⊙snd)) ⟩
    –> (A.eq (obj G (U ⊙× V)) (U ⊙× V)) (⊙fanout (<– (A.eq (obj G U ⊙× obj G V) U) ⊙fst) (<– (A.eq (obj G U ⊙× obj G V) V) ⊙snd)
    ⊙∘ arr F (⊙fanout (arr G ⊙fst) (arr G ⊙snd)))
      =⟨ ⊙fanout-pre∘ (<– (A.eq (obj G U ⊙× obj G V) U) ⊙fst) (<– (A.eq (obj G U ⊙× obj G V) V) ⊙snd)
           (arr F (⊙fanout (arr G ⊙fst) (arr G ⊙snd)))
         |in-ctx –> (A.eq _ _) ⟩
    –> (A.eq (obj G (U ⊙× V)) (U ⊙× V)) (⊙fanout
            (<– (A.eq (obj G U ⊙× obj G V) U) ⊙fst ⊙∘ arr F (⊙fanout (arr G ⊙fst) (arr G ⊙snd)))
            (<– (A.eq (obj G U ⊙× obj G V) V) ⊙snd ⊙∘ arr F (⊙fanout (arr G ⊙fst) (arr G ⊙snd))))
      =⟨ ap2 (λ f g → –> (A.eq (obj G (U ⊙× V)) (U ⊙× V)) (⊙fanout f g))
           (A.nat!-dom (⊙fanout (arr G ⊙fst) (arr G ⊙snd)) _ ⊙fst
            ∙ ap (<– (A.eq (obj G (U ⊙× V)) U)) (⊙fst-fanout (arr G ⊙fst) (arr G ⊙snd))
            ∙ ! (A.nat!-cod _ ⊙fst (⊙idf _)))
           (A.nat!-dom (⊙fanout (arr G ⊙fst) (arr G ⊙snd)) _ ⊙snd
            ∙ ap (<– (A.eq (obj G (U ⊙× V)) V)) (⊙snd-fanout (arr G ⊙fst) (arr G ⊙snd))
            ∙ ! (A.nat!-cod _ ⊙snd (⊙idf _))) ⟩
    –> (A.eq (obj G (U ⊙× V)) (U ⊙× V)) (⊙fanout (⊙fst ⊙∘ <– (A.eq (obj G (U ⊙× V)) (U ⊙× V)) (⊙idf _))
                                                 (⊙snd ⊙∘ <– (A.eq (obj G (U ⊙× V)) (U ⊙× V)) (⊙idf _)))
      =⟨ ap (–> (A.eq (obj G (U ⊙× V)) (U ⊙× V))) (! (⊙fanout-pre∘ ⊙fst ⊙snd (<– (A.eq (obj G (U ⊙× V)) (U ⊙× V)) (⊙idf _)))) ⟩
    –> (A.eq (obj G (U ⊙× V)) (U ⊙× V)) (⊙fanout ⊙fst ⊙snd ⊙∘ <– (A.eq (obj G (U ⊙× V)) (U ⊙× V)) (⊙idf _))
      =⟨ ⊙λ= (⊙∘-unit-l _) |in-ctx –> (A.eq (obj G (U ⊙× V)) (U ⊙× V)) ⟩
    –> (A.eq (obj G (U ⊙× V)) (U ⊙× V)) (<– (A.eq (obj G (U ⊙× V)) (U ⊙× V)) (⊙idf _))
      =⟨ <–-inv-r (A.eq (obj G (U ⊙× V)) (U ⊙× V)) (⊙idf _) ⟩
    ⊙idf _ =∎

  ⊙eq : obj G (U ⊙× V) ⊙≃ obj G U ⊙× obj G V
  ⊙eq = ≃-to-⊙≃ (equiv (fst ⊙into) (fst ⊙out)
                  (app= (ap fst ⊙into-out)) (app= (ap fst ⊙out-into)))
                (snd ⊙into)

  ⊙path = ⊙ua ⊙eq

{- Using the equivalence in RightAdjoint× we get a binary
 - "arr G2" : (X × Y → Z) → (G X × G Y → G Z)
 - and there is some kind of naturality wrt the (FX→Y)≃(X→GY) equivalence
 - (use case: from ⊙ap we get ⊙ap2) -}
module RightAdjointBinary {i j} {F : PtdFunctor i j} {G : PtdFunctor j i}
  (adj : HomAdjoint F G)
  where

  private
    module A = HomAdjoint adj
    module A× = RightAdjoint× adj

  arr2 : {X Y Z : Ptd j}
    → X ⊙× Y ⊙→ Z → obj G X ⊙× obj G Y ⊙→ obj G Z
  arr2 {X} {Y} {Z} f = arr G f ⊙∘ A×.⊙out X Y

  nat-cod : {X : Ptd i} {Y Z W : Ptd j}
    (r₁ : obj F X ⊙→ Y) (r₂ : obj F X ⊙→ Z)
    (o : Y ⊙× Z ⊙→ W)
    → –> (A.eq X W) (o ⊙∘ ⊙fanout r₁ r₂)
      == arr2 o ⊙∘ ⊙fanout (–> (A.eq X Y) r₁) (–> (A.eq X Z) r₂)
  nat-cod {X} {Y} {Z} {W} r₁ r₂ o =
    –> (A.eq X W) (o ⊙∘ ⊙fanout r₁ r₂)
      =⟨ ! (A.nat-cod X o (⊙fanout r₁ r₂)) ⟩
    arr G o ⊙∘ –> (A.eq X (Y ⊙× Z)) (⊙fanout r₁ r₂)
      =⟨ ! (A×.⊙out-into Y Z)
         |in-ctx (λ w → (arr G o ⊙∘ w) ⊙∘ –> (A.eq X (Y ⊙× Z)) (⊙fanout r₁ r₂)) ⟩
    (arr G o ⊙∘ (A×.⊙out Y Z ⊙∘ A×.⊙into Y Z))
    ⊙∘ –> (A.eq X (Y ⊙× Z)) (⊙fanout r₁ r₂)
      =⟨ ⊙∘-assoc-lemma (arr G o) (A×.⊙out Y Z) (A×.⊙into Y Z)
           (–> (A.eq X (Y ⊙× Z)) (⊙fanout r₁ r₂)) ⟩
    arr2 o ⊙∘ A×.⊙into Y Z ⊙∘ –> (A.eq X (Y ⊙× Z)) (⊙fanout r₁ r₂)
      =⟨ ⊙fanout-pre∘ (arr G ⊙fst) (arr G ⊙snd) (–> (A.eq X (Y ⊙× Z)) (⊙fanout r₁ r₂))
         |in-ctx (λ w → arr2 o ⊙∘ w) ⟩
    arr2 o ⊙∘ ⊙fanout (arr G ⊙fst ⊙∘ –> (A.eq X (Y ⊙× Z)) (⊙fanout r₁ r₂))
                      (arr G ⊙snd ⊙∘ –> (A.eq X (Y ⊙× Z)) (⊙fanout r₁ r₂))
      =⟨ ap2 (λ w₁ w₂ → arr2 o ⊙∘ ⊙fanout w₁ w₂)
           (A.nat-cod X ⊙fst (⊙fanout r₁ r₂)
            ∙ ap (–> (A.eq X Y)) (⊙fst-fanout r₁ r₂))
           (A.nat-cod X ⊙snd (⊙fanout r₁ r₂)
            ∙ ap (–> (A.eq X Z)) (⊙snd-fanout r₁ r₂)) ⟩
    arr2 o ⊙∘ ⊙fanout (–> (A.eq X Y) r₁) (–> (A.eq X Z) r₂) =∎
    where
    ⊙∘-assoc-lemma : ∀ {i j k l m}
      {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {U : Ptd l} {V : Ptd m}
      (k : U ⊙→ V) (h : Z ⊙→ U)
      (g : Y ⊙→ Z) (f : X ⊙→ Y)
      → (k ⊙∘ (h ⊙∘ g)) ⊙∘ f == (k ⊙∘ h) ⊙∘ g ⊙∘ f
    ⊙∘-assoc-lemma (k , idp) (h , idp) (g , idp) (f , idp) = idp

{- a left adjoint preserves wedges -}
module LeftAdjoint∨ {i j} {F : PtdFunctor i j} {G : PtdFunctor j i}
  (adj : HomAdjoint F G) (U V : Ptd i) where

  private
    module A = HomAdjoint adj

  module Into = ⊙WedgeRec (arr F {U} {U ⊙∨ V} ⊙winl) (arr F ⊙winr)

  ⊙into : obj F U ⊙∨ obj F V ⊙→ obj F (U ⊙∨ V)
  ⊙into = Into.⊙f

  module OutHelp = ⊙WedgeRec
    (–> (A.eq U (obj F U ⊙∨ obj F V)) ⊙winl)
    (–> (A.eq V (obj F U ⊙∨ obj F V)) ⊙winr)

  ⊙out : obj F (U ⊙∨ V) ⊙→ obj F U ⊙∨ obj F V
  ⊙out = <– (A.eq (U ⊙∨ V) (obj F U ⊙∨ obj F V)) OutHelp.⊙f

  ⊙into-out : ⊙into ⊙∘ ⊙out == ⊙idf (obj F (U ⊙∨ V))
  ⊙into-out =
    ⊙into ⊙∘ ⊙out
      =⟨ A.nat!-cod _ ⊙into (⊙Wedge-rec (–> (A.eq U (obj F U ⊙∨ obj F V)) ⊙winl)
                                        (–> (A.eq V (obj F U ⊙∨ obj F V)) ⊙winr)) ⟩
    <– (A.eq (U ⊙∨ V) (obj F (U ⊙∨ V))) (arr G ⊙into ⊙∘ ⊙Wedge-rec (–> (A.eq U (obj F U ⊙∨ obj F V)) ⊙winl)
                                             (–> (A.eq V (obj F U ⊙∨ obj F V)) ⊙winr))
      =⟨ ap (<– (A.eq (U ⊙∨ V) (obj F (U ⊙∨ V)))) $ ⊙λ= $
          ⊙Wedge-rec-post∘ (arr G ⊙into)
            (–> (A.eq U (obj F U ⊙∨ obj F V)) ⊙winl)
            (–> (A.eq V (obj F U ⊙∨ obj F V)) ⊙winr) ⟩
    <– (A.eq (U ⊙∨ V) (obj F (U ⊙∨ V))) (⊙Wedge-rec (arr G ⊙into ⊙∘ –> (A.eq U (obj F U ⊙∨ obj F V)) ⊙winl)
                                                    (arr G ⊙into ⊙∘ –> (A.eq V (obj F U ⊙∨ obj F V)) ⊙winr))
      =⟨ ap2 (λ w₁ w₂ → <– (A.eq (U ⊙∨ V) (obj F (U ⊙∨ V))) (⊙Wedge-rec w₁ w₂))
             (A.nat-cod _ ⊙into ⊙winl
              ∙ ap (–> (A.eq U (obj F (U ⊙∨ V)))) (Into.⊙winl-β ∙ ! (⊙λ= $ ⊙∘-unit-l _))
              ∙ ! (A.nat-dom ⊙winl _ (⊙idf _)))
             (A.nat-cod _ ⊙into ⊙winr
              ∙ ap (–> (A.eq V (obj F (U ⊙∨ V)))) (Into.⊙winr-β ∙ ! (⊙λ= $ ⊙∘-unit-l _))
              ∙ ! (A.nat-dom ⊙winr _ (⊙idf _))) ⟩
    <– (A.eq (U ⊙∨ V) (obj F (U ⊙∨ V))) (⊙Wedge-rec (–> (A.eq (U ⊙∨ V) (obj F (U ⊙∨ V))) (⊙idf _) ⊙∘ ⊙winl)
                                                    (–> (A.eq (U ⊙∨ V) (obj F (U ⊙∨ V))) (⊙idf _) ⊙∘ ⊙winr))
      =⟨ ap (<– (A.eq (U ⊙∨ V) (obj F (U ⊙∨ V)))) $ ! $ ⊙λ= $
            ⊙Wedge-rec-post∘ (–> (A.eq (U ⊙∨ V) (obj F (U ⊙∨ V))) (⊙idf _)) ⊙winl ⊙winr ⟩
    <– (A.eq (U ⊙∨ V) (obj F (U ⊙∨ V))) (–> (A.eq (U ⊙∨ V) (obj F (U ⊙∨ V))) (⊙idf _) ⊙∘ ⊙Wedge-rec ⊙winl ⊙winr)
      =⟨ ap (λ w → <– (A.eq (U ⊙∨ V) (obj F (U ⊙∨ V))) (–> (A.eq (U ⊙∨ V) (obj F (U ⊙∨ V))) (⊙idf _) ⊙∘ w))
            ⊙Wedge-rec-η ⟩
    <– (A.eq (U ⊙∨ V) (obj F (U ⊙∨ V))) (–> (A.eq (U ⊙∨ V) (obj F (U ⊙∨ V))) (⊙idf _))
      =⟨ <–-inv-l (A.eq (U ⊙∨ V) (obj F (U ⊙∨ V))) (⊙idf _) ⟩
    ⊙idf _ =∎

  ⊙out-into : ⊙out ⊙∘ ⊙into == ⊙idf _
  ⊙out-into =
    ⊙out ⊙∘ ⊙Wedge-rec (arr F ⊙winl) (arr F ⊙winr)
      =⟨ ⊙λ= $ ⊙Wedge-rec-post∘ ⊙out (arr F ⊙winl) (arr F ⊙winr) ⟩
    ⊙Wedge-rec (⊙out ⊙∘ arr F ⊙winl) (⊙out ⊙∘ arr F ⊙winr)
      =⟨ ap2 ⊙Wedge-rec
           (A.nat!-dom ⊙winl _ (⊙Wedge-rec _ _)
            ∙ ap (<– (A.eq U (obj F U ⊙∨ obj F V))) OutHelp.⊙winl-β
            ∙ <–-inv-l (A.eq U (obj F U ⊙∨ obj F V)) ⊙winl)
           (A.nat!-dom ⊙winr _ (⊙Wedge-rec _ _)
            ∙ ap (<– (A.eq V (obj F U ⊙∨ obj F V))) OutHelp.⊙winr-β
            ∙ <–-inv-l (A.eq V (obj F U ⊙∨ obj F V)) ⊙winr) ⟩
    ⊙Wedge-rec ⊙winl ⊙winr
      =⟨ ⊙Wedge-rec-η ⟩
    ⊙idf _ =∎

  ⊙eq : obj F U ⊙∨ obj F V ⊙≃ obj F (U ⊙∨ V)
  ⊙eq = ≃-to-⊙≃ (equiv (fst ⊙into) (fst ⊙out)
                  (app= (ap fst ⊙into-out)) (app= (ap fst ⊙out-into)))
                (snd ⊙into)

  ⊙path = ⊙ua ⊙eq
