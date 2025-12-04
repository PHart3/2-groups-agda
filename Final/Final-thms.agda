{-# OPTIONS --without-K --rewriting #-}

module Final-thms where

-- Owen Milner's equivalence between pointed connected n-types and Sính triples (with n ≥ 2)
open import Sinh-classif public
-- a description of the group action from the Sính triple of a given higher group
open import Sinh-action public

{- type equivalence between coherent 2-groups and pointed connected 2-types as well as
   composite type equivalence between coherent 2-groups and Sính triples -}
{- This file takes over an hour and up to 22 GB of memory to check. -}
open import Type-equiv-main public


-- explicit biadjoint biequivalence between 2-groups and pointed connected 2-types:

-- The following file checks the biequivalence data and takes over an hour and up to 29 GB of memory.
open import Biequiv-main public

{-
  The following file checks the triangulator for the above biequivalence, which takes signigicant
  extra time. Comment out the folloiwng line if you want to avoid checking it.
-}
open import Biadj-biequiv-main public

-- an equality between the same two (2,1)-categories obtained from the biadjoint biequivalence
open import Equality-main public
