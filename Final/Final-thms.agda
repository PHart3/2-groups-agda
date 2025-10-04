{-# OPTIONS --without-K --rewriting #-}

module Final-thms where

-- Owen Milner's equivalence between pointed connected n-types and Sính triples (with n ≥ 2)
open import Sinh-classif public

{- type equivalence between coherent 2-groups and pointed connected 2-types as well as
   composite type equivalence between coherent 2-groups and Sính triples -}
{- This file takes over an hour and up to 22 GB of memory to check. -}
open import Type-equiv-main public


{-
  The remaining two files take over an hour and up to 29 GB of memory to check.
  Comment out the following two imports to avoid checking them.
-}


-- explicit biequivalence between 2-groups and pointed connected 2-types
open import Biequiv-main public

-- an equality between the same two (2,1)-categories obtained from the biequivalence
open import Equality-main public
