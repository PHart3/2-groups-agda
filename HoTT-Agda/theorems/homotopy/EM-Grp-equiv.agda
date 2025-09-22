{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

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
