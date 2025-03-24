{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Truncation
open import lib.types.LoopSpace
open import lib.types.Int

-- Whitehead's theorem for truncated types 

{-
  The proof here is adapted from Dan Licata's proof
  (dated Jul 9, 2014) in his hott-agda library.
-}

module homotopy.Whitehead {i j : ULevel} where

  IsWEq : {A : Type i} {B : Type j} → (f : A → B) → Type
  IsWEq {A}{B} f = (y : B) → is-contr (hfiber f y)
  
  WEq : (A B : Type) → Type
  WEq A B = Σ \f → IsWEq{A}{B} f

  IsWeq≃IsEquiv : {A : Type i} {B : Type j} (f : A → B) → IsWEq f == is-equiv f
  IsWeq≃IsEquiv{A}{B} f = IsWEq f ≃〈id ⟩ 
                   ((y : B) → is-contr (Σ \x → Path (f x) y)) ≃〈 id ⟩ 
                   ((y : B) → Σ (\ (p : (Σ \x → Path (f x) y)) → ((q : (Σ \x → Path (f x) y)) → Path p q))) ≃〈 ΠΣcommute _ _ _ ⟩ 
                   Σ (λ (f' : (x : B) → Σ (λ x' → Path (f x') x)) → (x : B) (q : Σ (λ x' → Path (f x') x)) → Path (f' x) q) ≃〈 apΣ' (ΠΣcommuteEquiv _ _ _) (λ x' → id) ⟩ 
                   Σ (λ (f' : Σ (λ (g : B → A) → (x : B) → Path (f (g x)) x)) 
                      → (y : B) (q : Σ (λ (x : A) → Path (f x) y)) → Path (fst f' y , snd f' y) q)
                        ≃〈 ap (λ t → Σ {A = Σ (λ (g : B → A) → (x : B) → Path (f (g x)) x)} t) (λ≃ STS) ⟩ 
                   Σ (λ x → Σ (λ α → (x' : A) → snd x (f x') == ap f (α x'))) ≃〈 ! (IsEquiv-as-tuple≃ f) ⟩ 
                   is-equiv f =∎
                   where
    STS : (f' : Σ (λ (g : B → A) → (x : B) → Path (f (g x)) x)) → 
         ((y : B) (q : Σ (λ (x : A) → Path (f x) y)) → Path (fst f' y , snd f' y) q) 
        == Σ (λ α → (x : A) → snd f' (f x) == ap f (α x)) 
    STS f' = ((y : B) (q : Σ (λ (x : A) → Path (f x) y)) → Path (fst f' y , snd f' y) q) ==〈 ap (λ C → (y : B) → C y) (λ≃ (λ y → uncurry≃ A (λ x → Path (f x) y) _)) ⟩
             ((y : B) (x : A) (y' : Path (f x) y) → Path{Σ (λ v → Path (f v) y)} (fst f' y , snd f' y) (x , y')) ≃〈 exchange≃ ⟩
             ((x : A) (y : B) (y' : Path (f x) y) → Path{Σ (λ v → Path (f v) y)} (fst f' y , snd f' y) (x , y')) ≃〈 ap (λ B' → (x : A) → B' x) (λ≃ (λ x → path-induction≃)) ⟩
             ((x : A) → Path{Σ (λ v → Path (f v) (f x))} (fst f' (f x) , snd f' (f x)) (x , id)) ≃〈 ap (λ C → (x : A) → C x) (λ≃ (λ x → ! ΣPath.path)) ⟩
             ((x : A) → Σ (λ α → Path (transport (λ v → Path (f v) (f x)) α (snd f' (f x))) id)) ≃〈 ΠΣcommute _ _ _ ⟩ 
             Σ (λ (α : (x : A) → Path (fst f' (f x)) x) → (x : A) →
               Path (transport (λ v → Path (f v) (f x)) (α x) (snd f' (f x))) id)
               ≃〈 ap (λ C → Σ (λ (α : (x : A) → Path (fst f' (f x)) x) → C α)) (λ≃ (λ α → ap (λ C → (x : A) → C x) (λ≃ (λ x → STS' α x)))) ⟩ 
             Σ (λ α → (x : A) → snd f' (f x) == ap f (α x)) =∎ where
        STS' : (α : (x : A) → Path (fst f' (f x)) x) → 
               (x : A) 
             → Path (transport (λ v → Path (f v) (f x)) (α x) (snd f' (f x))) idp == (snd f' (f x) == ap f (α x)) 
        STS' α x =
          (transport (λ v → Path (f v) (f x)) (α x) (snd f' (f x)) == idp)
            =⟨ ap (BackPath _) (transport-Path-pre' f (α x) (snd f' (f x))) ⟩
          ((snd f' (f x) ∘ ! (ap f (α x))) == idp)
            =⟨ cancels-inverse-is≃ (snd f' (f x)) (ap f (α x)) ⟩
          ((snd f' (f x)) == (ap f (α x))) =∎

  module LoopEquivToPathEquiv {A : Type i} {B : Type j}
                              (f : A → B)
                              (zero : is-equiv (Trunc-fmap {n = tl 0} f))
                              (loops : (x : A) → is-equiv (ap f {x = x} {y = x})) where

    eqv : (x : A) (x' : A) (α : x == x') → is-equiv (ap f {x = x} {y = x'} )
    eqv x .x idp  = loops x

    paths' : (x : A) (x' : A) → IsWEq{(Path{A} x x')}{(Path{B} (f x) (f x'))} (ap f)
    paths' x x' β = Trunc-rec (contr-is-prop _)
                             (λ α → coe (! (IsWeq≃is-equiv (ap f))) (eqv x x' α) β)
                             fact2 where 
      fact1 : Path{Trunc (tl 0) A} ([ x ]) ([ x' ])
      fact1 = is-equiv.g-f zero [ x' ] ∘ ap (is-equiv.g zero) (ap [_] β) ∘ ! (is-equiv.g-f zero [ x ])

      fact2 : Trunc -1 (Path x x') 
      fact2 = coe (! (=ₜ-path-can -1)) fact1
{-
    abstract
      paths : (x : A) (x' : A) → is-equiv{(Path{A} x x')}{(Path{B} (f x) (f x'))} (ap f)
      paths x x' = coe (IsWeq≃is-equiv (ap f)) (paths' x x')
  

  module SplitEquiv {A : Type i} {B : Type j} 
                    (f : A → B)
                    (zero : is-equiv {Trunc (tl 0) A} {Trunc (tl 0) B} (Trunc-fmap f))
                    (one : (x : A) → is-equiv {(Path{A} x x)} {(Path{B} (f x) (f x))} (ap f))
         where

     one' : (x x' : A) → is-equiv {(Path{A} x x')} {(Path{B} (f x) (f x'))} (ap f)
     one' = LoopEquivToPathEquiv.paths f zero one

     iseqv' : IsWEq f 
     iseqv' y = gen tx tβ where
       tx : Trunc (tl 0) A 
       tx = is-equiv.g zero [ y ]

       tβ : Path{Trunc (tl 0) B} (Trunc-fmap f (is-equiv.g zero [ y ])) [ y ]
       tβ = is-equiv.f-g zero [ y ]

       gen : (x : Trunc (tl 0) A) → Path{Trunc (tl 0) B} (Trunc-fmap f x) [ y ] 
                → is-contr (HFiber f y)
       gen = Trunc-elim _ (λ _ → increment-level (Πlevel (λ _ → contr-is-prop _))) 
        (λ x tα →
          Trunc-rec (contr-is-prop _)
          (λ α → (x , α) , 
                 (λ {(x' , α') → pair≃ (is-equiv.g (one' x x') (! α' ∘ α))
                                       (transport (λ v → Path (f v) y) (is-equiv.g (one' x x') (! α' ∘ α)) α =⟨ transport-Path-pre' f (is-equiv.g (one' x x') (! α' ∘ α)) α ⟩ 
                                        α ∘ ! (ap f (is-equiv.g (one' x x') (! α' ∘ α))) =⟨ ap (λ x0 → α ∘ ! x0) (is-equiv.f-g (one' x x') (! α' ∘ α)) ⟩ 
                                        α ∘ ! (! α' ∘ α) =⟨ ap (λ x0 → α ∘ x0) (!-∘ (! α') α) ⟩ 
                                        α ∘ ! α ∘ ! (! α') =⟨ !-inv-r-front α (! (! α')) ⟩ 
                                        ! (! α') =⟨ !-invol α' ⟩ 
                                        α' =∎)}))
          (coe (! (=ₜ-path-can -1)) tα))

     iseqv : is-equiv f 
     iseqv = coe (IsWeq≃is-equiv f) iseqv'

  module Whitehead-NType where

    whitehead : {A : Type i} {B : Type j} (n : Positive) 
                (nA : NType (tlp n) A) (nB : NType (tlp n) B)
                (f : A → B)
                (zero : is-equiv {Trunc (tl 0) A} {Trunc (tl 0) B} (Trunc-fmap f))
                (pis  : ∀ k x → is-equiv{π k A x}{π k B (f x)} (Trunc-fmap (ap^ k f)))
              → is-equiv f
    whitehead One nA nB f zero pis = 
      SplitEquiv.iseqv f zero 
        (λ x →        snd (UnTrunc.eqv (tl 0) _ (use-level nB (f x) (f x))
               ∘e (Trunc-fmap (ap f) , pis One x)
               ∘e (!equiv (UnTrunc.eqv (tl 0) _ (use-level nA x x)))))
    whitehead {A}{B} (S n) nA nB f zero pis = SplitEquiv.iseqv f zero (λ x → IH x) where
      IH : (x : A) → is-equiv {Path x x}{Path (f x) (f x)} (ap f)
      IH x = whitehead n (use-level nA x x) (use-level nB (f x) (f x)) (ap f) 
                       (pis One x)
                       (λ k α → transport is-equiv (coe-incr-pis k α) (coe-is-equiv (incr-pis k α))) where 

              incr-pis : ∀ k α → (π k (Path {A} x x) α) == (π k (Path {B} (f x) (f x)) (ap f α))
              incr-pis k α = 
                 -- optimized proof-term
                    ap (Trunc (tl 0)) ((! (rebase-Loop-Path k (ap f α))) ∘ (LoopPath.path k))
                  ∘ ua (Trunc-fmap (ap^ (S k) f) , pis (S k) x)
                  ∘ ap (Trunc (tl 0)) ((! (LoopPath.path {A} {x} k)) ∘ (rebase-Loop-Path k α))
              {- legible version:
                π k (Path {A} x x) α =⟨ ap (Trunc (tl 0)) (rebase-Loop-Path k α) ⟩ 
                π k (Path {A} x x) idp =⟨ ap (Trunc (tl 0)) (! (LoopPath.path {A} {x} k)) ⟩ 
                π (S k) A x =⟨ ua (Trunc-fmap (ap^ (S k) f) , pis (S k) x) ⟩ 
                π (S k) B (f x) =⟨ ap (Trunc (tl 0)) (LoopPath.path k) ⟩ 
                π k (Path {B} (f x) (f x)) idp =⟨ ap (Trunc (tl 0)) (! (rebase-Loop-Path k (ap f α))) ⟩
                π k (Path {B} (f x) (f x)) (ap f α) =∎ 
              -}

              coe-incr-pis : ∀ k α → coe (incr-pis k α) == Trunc-fmap (ap^ k (ap f))
              coe-incr-pis k α = coe (incr-pis k α) =⟨ rearrange (ap^ (S k) f) (pis (S k) x) (! (rebase-Loop-Path k (ap f α))) (LoopPath.path k) (! (LoopPath.path {A} {x} k)) (rebase-Loop-Path k α)⟩ 
                                 Trunc-fmap (  coe (! (rebase-Loop-Path k (ap f α))) 
                                             o coe (LoopPath.path k)
                                             o (ap^ (S k) f) 
                                             o coe (! (LoopPath.path {A} {x} k))
                                             o coe (rebase-Loop-Path k α)) =⟨ ap Trunc-fmap STS ⟩
                                 Trunc-fmap (ap^ k (ap f)) =∎ where 
                rearrange : ∀ {A B C C' D E : Type} (f : C → C') (e : is-equiv (Trunc-fmap f))
                              (α1 : D == E) (α2 : C' == D) (α3 : B == C) (α4 : A == B) → 
                            coe (ap (Trunc (tl 0)) (α1 ∘ α2)
                                 ∘ ua (Trunc-fmap f , e)
                                 ∘ ap (Trunc (tl 0)) (α3 ∘ α4))
                            == Trunc-fmap (coe α1 o coe α2 o f o coe α3 o coe α4)
                rearrange f e idp idp idp idp = type≃β (Trunc-fmap f , e) ∘ ap coe (∘-unit-l (ua (Trunc-fmap f , e)))
    
                reduce-rebase-Loop-Path :
                          ∀ {x' : A} (α : x == x')
                             (fl : ∀ {x'} (α : x == x') 
                                   → Loop k (Path x x') α 
                                   → Loop k (Path (f x) (f x')) (ap f α))
                           → Path
                              (coe (! (rebase-Loop-Path k (ap f α))) o
                               fl idp o
                               coe (rebase-Loop-Path k α))
                              (fl α) 
                reduce-rebase-Loop-Path idp fl = id

                STS : (  coe (! (rebase-Loop-Path k (ap f α))) 
                       o coe (LoopPath.path k)
                       o (ap^ (S k) f) 
                       o coe (! (LoopPath.path {A} {x} k))
                       o coe (rebase-Loop-Path k α))
                      == (ap^ k (ap f))
                STS = coe (! (rebase-Loop-Path k (ap f α))) o
                      coe (LoopPath.path k) o
                      ap^ (S k) f o
                      coe (! (LoopPath.path {A} {x} k)) o
                      coe (rebase-Loop-Path k α) =⟨ ap2 (λ x' y → coe (! (rebase-Loop-Path k (ap f α))) o x' o ap^ (S k) f o y o coe (rebase-Loop-Path k α)) (type≃β (LoopPath.eqv k)) (type≃β! (LoopPath.eqv k)) ⟩ 

                      coe (! (rebase-Loop-Path k (ap f α))) o
                      loopSN1 k o ap^ (S k) f o loopN1S k o
                      coe (rebase-Loop-Path k α) =⟨ ap (λ x' → coe (! (rebase-Loop-Path k (ap f α))) o x' o coe (rebase-Loop-Path k α)) (! (λ≃ (ap^-ap-assoc k f))) ⟩ 

                      coe (! (rebase-Loop-Path k (ap f α))) o
                      (ap^ k (ap f)) o
                      coe (rebase-Loop-Path k α) =⟨ reduce-rebase-Loop-Path α (λ {x' : A} (α' : Path x x') (l : Loop k (Path x x') α') → ap^ k (ap f) l) ⟩
 
                      (ap^ k (ap f) =∎) 

-}
