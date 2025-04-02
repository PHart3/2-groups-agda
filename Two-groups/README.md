## Summary

This directory contains a formalized biequivalence between the
(2,1)-category of (cohernet) 2-groups and the (2,1)-category of
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
  proof of the associated delooping (`Decode-main.agda`).

- The `Bicats/` folder contains basic information about (2,1)-categories
  and pseudofunctors between them. It also contains a definition of a
  biequivalence between (2,1)-categories. Finally, it collects the data
  defining the two (2,1)-categories of interest.

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
  a biequivalence. The full biequivalence is defined in `Biequiv-main.agda`.

## Manual Type-Checking

1. Install Agda 2.6.4.3.
2. Install the stripped, modified HoTT-Agda library under `../HoTT-Agda`.
3. Type-check the file `Grp-Type-biequiv/Biequiv-main.agda`.

The type-checking of this file is very intensive. We have verfied that the type-checker
finishes successfully on the following machine:

*macOS Sequoia 15.4, Apple M1 chip, 16 GB of RAM*

The type-checking takes about 166.75 minutes in total. (See [stats.md](../stats.md).)
Note that macOS, unlike Linux, dynamically alters the size of the swap file as the
process runs. This is crucial because the type-checking uses around 100 GB of memory
at some points. Therefore, make sure to run the type-checker on a system with a lot
of virtual memory available.

## License

This work is released under Mozilla Public License 2.0.
See [LICENSE.txt](LICENSE.txt).
