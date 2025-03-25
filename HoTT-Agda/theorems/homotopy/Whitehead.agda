{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.NConnected
open import lib.NType2
open import lib.Equivalence2
open import lib.types.Pi
open import lib.types.Truncation
open import lib.types.LoopSpace
open import lib.types.TLevel
open import lib.groups.HomotopyGroup

-- Whitehead's theorem for truncated types 

{-
  The proof here is an updated version of Dan Licata's
  hott-agda proof (dated Jul 9, 2014), found at

  https://github.com/dlicata335/hott-agda/blob/master/homotopy/Whitehead.agda
-}

module homotopy.Whitehead {i : ULevel} where

  module LoopEquivToPathEquiv {A : Type i} {B : Type i}
                              (f : A → B)
                              (zero : is-equiv (Trunc-fmap {n = tl 0} f))
                              (loops : (x : A) → is-equiv (ap f {x = x} {y = x})) where

    eqv : (x : A) (x' : A) (α : x == x') → is-equiv (ap f {x = x} {y = x'})
    eqv x _ idp  = loops x

    paths' : (x : A) (x' : A) → is-contr-map {A = Path x x'} {Path (f x) (f x')} (ap f)
    paths' x x' β = Trunc-rec (λ α → equiv-is-contr-map (eqv x x' α) β) fact2
      where
      
      fact1 : Path {A = Trunc (tl 0) A} ([ x ]) ([ x' ])
      fact1 = is-equiv.g-f zero [ x' ] ∙ʳ ap (is-equiv.g zero) (ap [_] β) ∙ʳ ! (is-equiv.g-f zero [ x ])

      fact2 : Trunc -1 (Path x x') 
      fact2 = –> (=ₜ-equiv-can -1) fact1

    abstract
      paths : (x : A) (x' : A) → is-equiv {A = Path x x'} {Path (f x) (f x')} (ap f)
      paths x x' = contr-map-is-equiv (paths' x x')
  
  module SplitEquiv {A : Type i} {B : Type i} 
                    (f : A → B)
                    (zero : is-equiv {A = Trunc (tl 0) A} {Trunc (tl 0) B} (Trunc-fmap f))
                    (one : (x : A) → is-equiv {A = Path x x} {Path (f x) (f x)} (ap f)) where

     one' : (x x' : A) → is-equiv {A = Path x x'} {Path (f x) (f x')} (ap f)
     one' = LoopEquivToPathEquiv.paths f zero one

     iseqv' : is-contr-map f 
     iseqv' y = gen tx tβ where
       tx : Trunc (tl 0) A 
       tx = is-equiv.g zero [ y ]

       tβ : Path {A = Trunc (tl 0) B} (Trunc-fmap f (is-equiv.g zero [ y ])) [ y ]
       tβ = is-equiv.f-g zero [ y ]

       gen : (x : Trunc (tl 0) A) →
         Path {A = Trunc (tl 0) B} (Trunc-fmap f x) [ y ] → is-contr (hfiber f y)
       gen = Trunc-elim
         (λ x tα → has-level-in
           (Trunc-rec (λ α → (x , α) , 
             (λ {(x' , α') →
               pair=-tr (is-equiv.g (one' x x') (! α' ∙ʳ α))
                 (transport (λ v → Path (f v) y) (is-equiv.g (one' x x') (! α' ∙ʳ α)) α
                   =ᵣ⟨ transport-Path-pre' {f = f} (is-equiv.g (one' x x') (! α' ∙ʳ α)) α ⟩ 
                 α ∙ʳ ! (ap f (is-equiv.g (one' x x') (! α' ∙ʳ α)))
                   =ᵣ⟨ ap (λ x0 → α ∙ʳ ! x0) (is-equiv.f-g (one' x x') (! α' ∙ʳ α)) ⟩ 
                 α ∙ʳ ! (! α' ∙ʳ α)
                   =ᵣ⟨ ap (λ x0 → α ∙ʳ x0) (!-∙ʳ (! α') α) ⟩ 
                 α ∙ʳ ! α ∙ʳ ! (! α')
                   =ᵣ⟨ !-inv-r-front α (! (! α')) ⟩ 
                 ! (! α')
                   =ᵣ⟨ !-! α' ⟩ 
                 α' =∎)}))
             (–> (=ₜ-equiv-can -1) tα)))

     iseqv : is-equiv f 
     iseqv = contr-map-is-equiv iseqv'

  module Whitehead-NType where

    abstract
      whitehead : {A : Type i} {B : Type i} (n : ℕ-ₚ) {{nA : has-level (tlp n) A}} {{nB : has-level (tlp n) B}}
        (f : A → B)
        (zero : is-equiv {A = Trunc (tl 0) A} {Trunc (tl 0) B} (Trunc-fmap f))
        (pis  : ∀ k x → is-equiv {A = π-tyₚ k A x} {π-tyₚ k B (f x)} (Trunc-fmap (Ω^-fmapₚ k f)))
        → is-equiv f
      whitehead I f zero pis =
        SplitEquiv.iseqv f zero 
          (λ x →
            snd (unTrunc-equiv {n = tl 0} _ ∘e
            (Trunc-fmap (ap f) , pis I x) ∘e
            (unTrunc-equiv {n = tl 0} _)⁻¹))
      whitehead {A} {B} (S n) f zero pis = SplitEquiv.iseqv f zero IH where
        IH : (x : A) → is-equiv {A = Path x x} {Path (f x) (f x)} (ap f)
        IH x = whitehead n (ap f) (pis I x)
          (λ k α → transport is-equiv (coe-incr-pis k α) (coe-is-equiv (incr-pis k α))) where 
            incr-pis : ∀ k α → π-tyₚ k (Path x x) α == π-tyₚ k (Path (f x) (f x)) (ap f α)
            incr-pis k α = 
              -- optimized proof-term
              ap (Trunc (tl 0)) ((! (rebase-Loop-Path (pnat k) (ap f α))) ∙ʳ
              Ω^-Ω-split-Path-ₚ k) ∙ʳ
              ua (Trunc-fmap (Ω^-fmapₚ (S k) f) , pis (S k) x) ∙ʳ
              ap (Trunc (tl 0)) ((! (Ω^-Ω-split-Path-ₚ {X = A} {x} k)) ∙ʳ
              rebase-Loop-Path (pnat k) α)
                {- legible version:
                  π-tyₚ k (Path {A} x x) α =ᵣ⟨ ap (Trunc (tl 0)) (rebase-Loop-Path (pnat k) α) ⟩ 
                  π-tyₚ k (Path {A} x x) idp =ᵣ⟨ ap (Trunc (tl 0)) (! (Ω^-Ω-split-Path-ₚ {X = A} {x} k)) ⟩ 
                  π-tyₚ (S k) A x =ᵣ⟨ ua (Trunc-fmap (Ω^-fmapₚ (S k) f) , pis (S k) x) ⟩ 
                  π-tyₚ (S k) B (f x) =ᵣ⟨ ap (Trunc (tl 0)) (Ω^-Ω-split-Path-ₚ k) ⟩ 
                  π-tyₚ k (Path {B} (f x) (f x)) idp =ᵣ⟨ ap (Trunc (tl 0)) (! (rebase-Loop-Path (pnat k) (ap f α))) ⟩
                  π-tyₚ k (Path {B} (f x) (f x)) (ap f α) =∎ 
                -}

            coe-incr-pis : ∀ k α → coe (incr-pis k α) == Trunc-fmap (Ω^-fmapₚ k (ap f))
            coe-incr-pis k α =
              coe (incr-pis k α)
                =ᵣ⟨ rearrange (Ω^-fmapₚ (S k) f) (pis (S k) x)
                      (! (rebase-Loop-Path (pnat k) (ap f α))) (Ω^-Ω-split-Path-ₚ k) (! (Ω^-Ω-split-Path-ₚ {X = A} {x} k))
                      (rebase-Loop-Path (pnat k) α) ⟩ 
              Trunc-fmap ( coe (! (rebase-Loop-Path (pnat k) (ap f α))) ∘
                           coe (Ω^-Ω-split-Path-ₚ k) ∘
                           Ω^-fmapₚ (S k) f ∘
                           coe (! (Ω^-Ω-split-Path-ₚ {X = A} {x} k)) ∘
                           coe (rebase-Loop-Path (pnat k) α))
                =ᵣ⟨ ap Trunc-fmap STS ⟩
              Trunc-fmap (Ω^-fmapₚ k (ap f)) =∎ where
              
                rearrange : ∀ {A B C C' D E : Type i} (f : C → C') (e : is-equiv (Trunc-fmap f))
                              (α1 : D == E) (α2 : C' == D) (α3 : B == C) (α4 : A == B) → 
                            coe (ap (Trunc (tl 0)) (α1 ∙ʳ α2) ∙ʳ ua (Trunc-fmap f , e) ∙ʳ ap (Trunc (tl 0)) (α3 ∙ʳ α4))
                              ==
                            Trunc-fmap (coe α1 ∘ coe α2 ∘ f ∘ coe α3 ∘ coe α4)
                rearrange f e idp idp idp idp = type≃β (Trunc-fmap f , e) ∙ʳ ap coe (∙ʳ-unit-l (ua (Trunc-fmap f , e)))

                reduce-rebase-Loop-Path : ∀ {x' : A} (α : x == x') (fl : ∀ {x'} (α : x == x')
                  → Ω^ (pnat k) (⊙[ x == x' , α ])
                  → Ω^ (pnat k) (⊙[ f x == f x' , ap f α ]))
                  → Path
                      (coe (! (rebase-Loop-Path (pnat k) (ap f α))) ∘ fl idp ∘ coe (rebase-Loop-Path (pnat k) α))
                      (fl α) 
                reduce-rebase-Loop-Path idp fl = idp

                STS : (coe (! (rebase-Loop-Path (pnat k) (ap f α))) ∘
                       coe (Ω^-Ω-split-Path-ₚ k) ∘
                       Ω^-fmapₚ (S k) f ∘
                       coe (! (Ω^-Ω-split-Path-ₚ {X = A} {x} k)) ∘
                       coe (rebase-Loop-Path (pnat k) α))
                         ==
                       Ω^-fmapₚ k (ap f)
                STS = coe (! (rebase-Loop-Path (pnat k) (ap f α))) ∘
                      coe (Ω^-Ω-split-Path-ₚ k) ∘
                      Ω^-fmapₚ (S k) f ∘
                      coe (! (Ω^-Ω-split-Path-ₚ {X = A} {x} k)) ∘
                      coe (rebase-Loop-Path (pnat k) α)
                        =ᵣ⟨ ap2 (λ x' y →
                                  coe (! (rebase-Loop-Path (pnat k) (ap f α))) ∘
                                  x' ∘
                                  Ω^-fmapₚ (S k) f ∘
                                  y ∘
                                  coe (rebase-Loop-Path (pnat k) α))
                              (type≃β (Ω^-Ω-split-≃-ₚ k))
                              (type≃β! (Ω^-Ω-split-≃-ₚ k)) ⟩ 
                      coe (! (rebase-Loop-Path (pnat k) (ap f α))) ∘
                      (Ω^-Ω-splitₚ k ∘ Ω^-fmapₚ (S k) f ∘ Ω^-Ω-split-revₚ k) ∘
                      coe (rebase-Loop-Path (pnat k) α)
                        =ᵣ⟨ ap (λ x' → coe (! (rebase-Loop-Path (pnat k) (ap f α))) ∘ x' ∘ coe (rebase-Loop-Path (pnat k) α))
                              (λ= (Ω^-ap-assoc-ₚ k f)) ⟩ 
                      coe (! (rebase-Loop-Path (pnat k) (ap f α))) ∘
                      Ω^-fmapₚ k (ap f) ∘
                      coe (rebase-Loop-Path (pnat k) α)
                        =ᵣ⟨ reduce-rebase-Loop-Path α
                              (λ {x' : A} (α' : Path x x') (l : Ω^ (pnat k) ⊙[ x == x' , α' ]) → Ω^-fmapₚ k (ap f) l) ⟩
                      Ω^-fmapₚ k (ap f) =∎

      -- corollary of whitehead for pointed maps on connected types
      whitehead⊙ : {A : Ptd i} {B : Ptd i} (n : ℕ-ₚ) {{nA : has-level (tlp n) (de⊙ A)}} {{cA : is-connected 0 (de⊙ A)}}
        {{nB : has-level (tlp n) (de⊙ B)}} (f : A ⊙→ B)
        (zero : is-equiv {A = Trunc (tl 0) (de⊙ A)} {Trunc (tl 0) (de⊙ B)} (Trunc-fmap (fst f)))
        (pis  : ∀ k → is-equiv {A = π-tyₚ k (de⊙ A) (pt A)} {π-tyₚ k (de⊙ B) (pt B)} (Trunc-fmap (fst (⊙Ω^-fmapₚ k f))))
        → is-equiv (fst f)
      whitehead⊙ {A} n (f₀ , idp) zero pis = whitehead n f₀ zero $
        λ k x → Trunc-rec {n = -1} (λ (α : pt A == x) → aux k α) (conn-path-conn (pt A) x)
          where
            aux : (k : ℕ-ₚ) {z : de⊙ A} (p : pt A == z) → is-equiv (Trunc-fmap {n = 0} (Ω^-fmapₚ k {z} f₀))
            aux k idp = pis k

  open Whitehead-NType public

  module _ {X Y : Ptd i} (f : X ⊙→ Y)
    {{tX : has-level 2 (de⊙ X)}} {{tY : has-level 2 (de⊙ Y)}} {{cX : is-connected 0 (de⊙ X)}} {{cY : is-connected 0 (de⊙ Y)}}
    where

    abstract
      02-Ω-equiv-whitehead : is-equiv (Ω-fmap f) → is-equiv (fst f)
      02-Ω-equiv-whitehead e = whitehead⊙ (S I) f (contr-to-contr-is-equiv (Trunc-fmap (fst f)) cX cY)
        (λ { I → Trunc-isemap e ;
             (S I) → Trunc-isemap (Ω-isemap (⊙Ω-fmap f) e) ;
             k@(S (S n)) →
               contr-to-contr-is-equiv (Trunc-fmap (fst (⊙Ω^-fmapₚ k f)))
                 (πS->level-contr-ₚ (S n) 2 X (<T-aux n))
                 (πS->level-contr-ₚ (S n) 2 Y (<T-aux n)) })
                 where  -- Agsy handles this lemma easily.
                   <T-aux : (n : ℕ-ₚ) →  S (S (S (S ⟨-2⟩))) <T S (S (S (S ⟨ pnat n ⟩₋₂)))
                   <T-aux I = ltS
                   <T-aux (S n) = ltSR (<T-aux n)
