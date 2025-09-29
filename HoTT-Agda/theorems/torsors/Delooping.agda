{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import lib.FTID
open import lib.types.Torsor

-- The type of torsors over a pointed type X as the delooping of X

module torsors.Delooping where

module _ {i j : ULevel} (X : Ptd i) {{c : is-contr (PtdTorsors j X)}} where

  
