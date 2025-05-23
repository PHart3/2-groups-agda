## Summary

This directory contains a formalized biequivalence between the
(2,1)-category of (coherent) 2-groups and the (2,1)-category of
pointed connected 2-types.


## Organization

- The `2Grps/` folder contains basic definitions, examples, and
  properties of 2-groups and morphisms between them. It also
  contains a proof (found in `2GrpHomEq.agda`) of the equivalence
  between the type of morphisms explicitly respecting all 2-group
  data and the type of those respecting just the tensor product
  and the associator.

- The `Deloop/` folder contains the HIT defining the classifying
  space of a 2-group (`Delooping.agda`) as well as an encode-decode
  proof of the associated delooping (`Delooping-equiv.agda`). To postulate
  the elimination principle for the HIT, we use  higher dependent path
  types defined in `../HoTT-Agda/core/lib/cubical/PathPathOver.agda`.
  We derive the recursion principle from the elimination principle.

- The `Bicat-stuff/` folder collects the data defining the two (2,1)-categories
  of interest. It also shows how to construct adjoint equivalences inside them.

- The `KFunc/` folder contains constructions making the delooping into
  a pseudofunctor from 2-groups to pointed connected 2-types along with
  associated proofs of coherence of these constructions.

- The `LoopFunc/` folder contains constructions making the LoopSpace into
  a pseudofunctor from pointed connected 2-types to 2-groups along with
  associated proofs of coherence of these constructions. The object function
  of the LoopSpace pseudofunctor is defined in `Hmtpy2Grp.agda`.

- The `Grp-Type-biequiv/` folder contains the proof of our desired biequivalence.
  The two arrows of the biequivalence are defined by the delooping and LoopSpace
  functors, and the bulk of this folder provides proofs of the associated
  pseudotransformations between their composites and the identity pseudofunctors.
  It also provides proofs exhibiting these pseudotransformations as levelwise
  adjoint equivalences (`LoopK-adjeq.agda` and `KLoop-adjeq.agda`), thereby forming
  a biequivalence. The full biequivalence is defined in `Biequiv-main.agda`. We also
  obtain an equality between the two (2,1)-categories in question by way of univalence
  (`Equality-main.agda`). This equality relies on the fact that every biequivalence
  between quasi-univalent bicategories is fully-faithful, which we prove in `../Bicats/`.

## License

This work is released under Mozilla Public License 2.0.
See [LICENSE.txt](LICENSE.txt).
