{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import HoTT
open import lib.wild-cats.WildCats
open import lib.types.Pointed-seq
open import homotopy.HSpace renaming (HSpaceStructure to HSS)
open import homotopy.Freudenthal
open import homotopy.IterSuspensionStable
import homotopy.Pi2HSusp as Pi2HSusp
open import homotopy.EM1HSpace
open import homotopy.EilenbergMacLane1
open import homotopy.EilenbergMacLane
open import homotopy.SuspAdjointLoop
open import homotopy.EM-gen-rec

-- type equivalence between set-level groups and pointed n-connected, (n+1)-types

module homotopy.EM-Grp-equiv {i} (G : AbGroup i) where

open AbGroup G
open EMExplicit G
open HSpace

open ⊙EM-β G

abstract
  ⊙EM-elim₂-β-deloop : (n : ℕ) {X : Ptd i} {{X-level : has-level ⟨ S (S n) ⟩ (de⊙ X)}} (φ : grp →ᴳ Ω^'S-group (S n) X)
    → GroupHom.⊙f φ ⊙◃∙ ⊙–> (deloop'-fold (S n)) ⊙◃∎ ⊙=ₛ ⊙Ω^'-fmap (S n) (⊙EM-elimₙ G n φ) ⊙◃∎
  ⊙EM-elim₂-β-deloop O φ =
    GroupHom.⊙f φ ⊙◃∙ ⊙–> (deloop'-fold 1) ⊙◃∎
      ⊙=ₛ⟨ 0 & 1 & ⊙=ₛ-in (! (EM₁Level₁Rec.⊙β-tri idp φ)) ⟩
    ⊙Ω-fmap (EM₁-level₁-rec idp φ , idp) ⊙◃∙ ⊙emloop ⊙◃∙ ⊙–> (deloop'-fold 1) ⊙◃∎
      ⊙=ₛ⟨ 2 & 1 & ⊙=ₛ-in idp ⟩
    ⊙Ω-fmap (EM₁-level₁-rec idp φ , idp) ⊙◃∙ ⊙emloop ⊙◃∙ ⊙–> (GroupIso.⊙f-equiv (Ω¹-EM₁ grp)) ⊙◃∙ ⊙–> Spectrum.spectrum0 ⊙◃∎
      ⊙=ₛ₁⟨ 1 & 2 & ⊙λ= ((<–-inv-r (emloop-equiv grp)) , prop-has-all-paths-↓ {{has-level-apply-instance {{has-level-apply-instance {{EM₁-level₁ grp}}}}}}) ⟩
    ⊙Ω-fmap (EM₁-level₁-rec idp φ , idp) ⊙◃∙ ⊙idf (⊙Ω (⊙EM₁ grp)) ⊙◃∙ ⊙–> Spectrum.spectrum0 ⊙◃∎
      ⊙=ₛ₁⟨ 0 & 2 & idp ⟩
    ⊙Ω-fmap (EM₁-level₁-rec idp φ , idp) ⊙◃∙ ⊙–> Spectrum.spectrum0 ⊙◃∎
      ⊙=ₛ⟨ 1 & 1 & ⊙=ₛ-in idp ⟩
    ⊙Ω-fmap (EM₁-level₁-rec idp φ , idp) ⊙◃∙
    ⊙–> (⊙unTrunc-equiv (⊙Ω (⊙EM₁ grp)) {{has-level-apply-instance {{EM₁-level₁ grp}}}}) ⊙◃∙
    ⊙Ω-Trunc-[_] (⊙EM₁ grp) ⊙◃∎
      ⊙=ₛ⟨ 1 & 2 & ⊙=ₛ-in (⊙-comp-to-== ({!!} , {!!})) ⟩
    ⊙Ω-fmap (EM₁-level₁-rec idp φ , idp) ⊙◃∙ ⊙Ω-fmap (⊙–> (⊙unTrunc-equiv (⊙EM₁ (fst G)) {{EM₁-level₁ grp}})) ⊙◃∎
      ⊙=ₛ₁⟨ ! (⊙Ω-fmap-∘ (EM₁-level₁-rec idp φ , idp) (⊙–> (⊙unTrunc-equiv (⊙EM₁ (fst G)) {{EM₁-level₁ grp}}))) ⟩
    ⊙Ω-fmap ((EM₁-level₁-rec idp φ ∘ –> (unTrunc-equiv (EM₁ (fst G)) {{EM₁-level₁ grp}})) , idp) ⊙◃∎ ⊙∎ₛ
  ⊙EM-elim₂-β-deloop (S n) φ = {!Ω^-level!}
