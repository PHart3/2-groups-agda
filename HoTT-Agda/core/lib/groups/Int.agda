{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Int
open import lib.types.Group
open import lib.groups.Homomorphism

module lib.groups.Int where

ℤ-group-structure : GroupStructure ℤ
ℤ-group-structure = record
  { ident = 0
  ; inv = ℤ~
  ; comp = _ℤ+_
  ; unit-l = ℤ+-unit-l
  ; assoc = ℤ+-assoc
  ; inv-l = ℤ~-inv-l
  }

ℤ-group : Group₀
ℤ-group = group _ ℤ-group-structure

ℤ-group-is-abelian : is-abelian ℤ-group
ℤ-group-is-abelian = ℤ+-comm

ℤ-abgroup : AbGroup₀
ℤ-abgroup = ℤ-group , ℤ-group-is-abelian
exp-shom : ∀ {i} {GEl : Type i} (GS : GroupStructure GEl) (g : GEl) → ℤ-group-structure →ᴳˢ GS
exp-shom GS g = group-structure-hom (GroupStructure.exp GS g) (GroupStructure.exp-+ GS g)

exp-hom : ∀ {i} (G : Group i) (g : Group.El G) → ℤ-group →ᴳ G
exp-hom G g = group-hom (Group.exp G g) (Group.exp-+ G g)
