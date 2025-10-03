{-# OPTIONS --without-K --rewriting #-}

module Final-thms where

-- Owen Milner's proof of equivalence between pointed connected n-types and Sinh triples (with n ≥ 2)
open import Sinh-classif public

{-
  type equivalence between coherent 2-groups and pointed connected 2-types as well as
  composite type equivalence between coherent 2-groups and Sinh triples
-}
open import Type-equiv-main public  -- this will take some time


{- Comment out the following lines to avoid massively long type-checking. -}


-- explicit biequivalence between 2-groups and pointed connected 2-types
open import Biequiv-main public

-- an equality between the same two (2,1)-categories obtained from the biequivalence
open import Equality-main public
