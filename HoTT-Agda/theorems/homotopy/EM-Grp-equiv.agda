{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import HoTT
open import lib.types.Pointed-seq
open import homotopy.HSpace renaming (HSpaceStructure to HSS)
open import homotopy.Freudenthal
open import homotopy.IterSuspensionStable
import homotopy.Pi2HSusp as Pi2HSusp
open import homotopy.EM1HSpace
open import homotopy.EilenbergMacLane1
open import homotopy.EilenbergMacLane
open import homotopy.SuspAdjointLoop

-- type equivalence between set-level groups and pointed n-connected, (n+1)-types

module homotopy.EM-Grp-equiv {i} (G : AbGroup i) where

open AbGroup G
open EMExplicit G

-- recursion principle for K(G, n)
⊙EM-elimₙ : (n : ℕ) {j : ULevel} {X : Ptd j} {{X-level : has-level ⟨ S n ⟩ (de⊙ X)}}
  → (grp →ᴳ Ω^'S-group n X) → ⊙EM (S n) ⊙→ X
⊙EM-elimₙ O {X = X@(⊙[ X₀ , pt ])} φ = (f ∘ –> (unTrunc-equiv (EM₁ (fst G)) {{EM₁-level₁ grp}})) , idp
  where open EM₁Level₁Rec pt φ
⊙EM-elimₙ (S n) {X = X} φ =
  ⊙Trunc-rec (ε X ⊙∘ ⊙Susp-fmap (⊙EM-elimₙ n {X = ⊙Ω X} φ) ⊙∘ ⊙Susp-fmap {X = ⊙Susp^ n (⊙EM₁ grp)} [_]-⊙)

open HSpace

module ⊙EM-β (n : ℕ) {X : Ptd i} {{X-level : has-level ⟨ S (S n) ⟩ (de⊙ X)}}
  (φ : grp →ᴳ Ω^'S-group (S n) X) where

  abstract
    ⊙EM-elimₙ-β : ⊙Ω-fmap (⊙EM-elimₙ (S n) φ) ⊙◃∙ ⊙<– (spectrum (S n)) ⊙◃∎ ⊙=ₛ ⊙EM-elimₙ n {X = ⊙Ω X} φ ⊙◃∎
    ⊙EM-elimₙ-β = let τ = (ε X ⊙∘ ⊙Susp-fmap (⊙EM-elimₙ n {X = ⊙Ω X} φ) ⊙∘ ⊙Susp-fmap {X = ⊙Susp^ n (⊙EM₁ grp)} [_]-⊙) in
      ⊙Ω-fmap (⊙EM-elimₙ (S n) φ) ⊙◃∙ ⊙<– (spectrum (S n)) ⊙◃∎
        ⊙=ₛ⟨ 1 & 1 & {!!} ⟩
      ⊙Ω-fmap (⊙EM-elimₙ (S n) φ) ⊙◃∙ ⊙Ω-UnTrunc-[_] (⊙Susp (⊙Susp^ n (⊙EM₁ grp))) ⊙◃∙ ⊙Trunc-fmap (η (⊙Susp^ n (⊙EM₁ grp))) ⊙◃∎
        ⊙=ₛ₁⟨ 0 & 1 & idp ⟩
      ⊙Ω-fmap (⊙Trunc-rec τ) ⊙◃∙ ⊙Ω-UnTrunc-[_] (⊙Susp (⊙Susp^ n (⊙EM₁ grp))) ⊙◃∙ ⊙Trunc-fmap (η (⊙Susp^ n (⊙EM₁ grp))) ⊙◃∎
        ⊙=ₛ⟨ 0 & 1 & ⊙=ₛ-in (! (⊙Ω-Trunc-rec-coh τ)) ⟩
      ⊙–> (⊙unTrunc-equiv (⊙Ω X)) ⊙◃∙
      ⊙Trunc-fmap (⊙Ω-fmap (ε X ⊙∘ ⊙Susp-fmap (⊙EM-elimₙ n φ) ⊙∘ ⊙Susp-fmap {X = ⊙Susp^ n (⊙EM₁ grp)} [_]-⊙)) ⊙◃∙
      ⊙Ω-Trunc-[_] (⊙Susp (⊙Susp^ n (⊙EM₁ grp))) ⊙◃∙
      ⊙Ω-UnTrunc-[_] (⊙Susp (⊙Susp^ n (⊙EM₁ grp))) ⊙◃∙
      ⊙Trunc-fmap (η (⊙Susp^ n (⊙EM₁ grp))) ⊙◃∎
        ⊙=ₛ⟨ 1 & 1 & ⊙=ₛ-in $
             ap ⊙Trunc-fmap (⊙Ω-fmap-∘-tri (ε X) (⊙Susp-fmap (⊙EM-elimₙ n φ)) (⊙Susp-fmap {X = ⊙Susp^ n (⊙EM₁ grp)} [_]-⊙)) ∙
             ! (⊙Trunc-∘-tri (⊙Ω-fmap (ε X)) (⊙Ω-fmap (⊙Susp-fmap (⊙EM-elimₙ n φ))) (⊙Ω-fmap (⊙Susp-fmap [_]-⊙))) ⟩
      ⊙–> (⊙unTrunc-equiv (⊙Ω X)) ⊙◃∙
      ⊙Trunc-fmap (⊙Ω-fmap (ε X)) ⊙◃∙
      ⊙Trunc-fmap (⊙Ω-fmap (⊙Susp-fmap (⊙EM-elimₙ n φ))) ⊙◃∙
      ⊙Trunc-fmap (⊙Ω-fmap (⊙Susp-fmap {X = ⊙Susp^ n (⊙EM₁ grp)} [_]-⊙)) ⊙◃∙
      ⊙Ω-Trunc-[_] (⊙Susp (⊙Susp^ n (⊙EM₁ grp))) ⊙◃∙
      ⊙Ω-UnTrunc-[_] (⊙Susp (⊙Susp^ n (⊙EM₁ grp))) ⊙◃∙
      ⊙Trunc-fmap (η (⊙Susp^ n (⊙EM₁ grp))) ⊙◃∎
        ⊙=ₛ⟨ {!⊙–> (⊙unTrunc-equiv (⊙Ω X)) !} ⟩
      {!!}
{-
  abstract
    ⊙EM-elim₂-β-rot : ⊙Ω-fmap (⊙EM-elimₙ (S n) φ) == ⊙EM-elimₙ n {X = ⊙Ω X} φ ⊙∘ ⊙–> (spectrum (S n))
    ⊙EM-elim₂-β-rot = 
      ⊙Ω-fmap (⊙EM-elimₙ (S n) φ)
        =⟨ ap (λ m → ⊙Ω-fmap (⊙EM-elimₙ (S n) φ) ⊙∘ m) (! (⊙λ= (⊙<–-inv-l (spectrum (S n))))) ⟩
      ⊙Ω-fmap (⊙EM-elimₙ (S n) φ) ⊙∘ ⊙<– (spectrum (S n)) ⊙∘ ⊙–> (spectrum (S n))
        =⟨ ! (⊙λ= (⊙∘-assoc (⊙Ω-fmap (⊙EM-elimₙ (S n) φ)) (⊙<– (spectrum (S n))) (⊙–> (spectrum (S n))))) ⟩
      (⊙Ω-fmap (⊙EM-elimₙ (S n) φ) ⊙∘ ⊙<– (spectrum (S n))) ⊙∘ ⊙–> (spectrum (S n))
        =⟨ ap (λ m → m ⊙∘ ⊙–> (spectrum (S n))) (⊙=ₛ-out ⊙EM-elimₙ-β) ⟩
      ⊙EM-elimₙ n {X = ⊙Ω X} φ ⊙∘ ⊙–> (spectrum (S n)) =∎
-}
