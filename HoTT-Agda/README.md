Homotopy Type Theory in Agda
============================

This directory contains a somewhat stripped-down version of Andrew Swan's [branch](https://github.com/awswan/HoTT-Agda/tree/agda-2.6.1-compatible) of the
HoTT-Agda library. It has been customized and significantly augmented to accommodate
our development of 2-groups and pointed types.

Setup
-----

The library is compatible with Agda 2.6.4.3. To use it, include `hott-core.agda-lib` and `hott-theorems.agda-lib` in your Agda libraries file.

Agda Options
------------

Each Agda file should have `--without-K --rewriting` in its header.
`--without-K` is for restricting pattern matching so that the uniqueness of identity proofs is not admissible.
`--rewriting` is for the computational rules of the higher inductive types.

Moreover, files postulating HITs should have `--confluence-check` in their headers. This ensures that the
new rewriting rules keep the system confluent, so that type-checking remains at least semi-decidable.

Structure of the source
-----------------------

### Core library (directory `core/lib/`)

The main library is more or less divided into four parts.

- The first part is exported in the module `lib.Basics` and contains essential constructions.
- The second part is found in `lib.groups` and develops basic group theory.
- The third part is found in `lib.types` and develops type formers.
- The fourth part is found in `lib.wild-cats` and develops wild category theory.
  In particular, it shows that every half-adjoint equivalence of wild categories (and its inverse) is fully faithful.

### Theorems (directory `theorems/`)

#### torsors

This directory contains David Wärn's construction of torsors as the unique connected delooping.
(See the paper "Eilenberg-MacLane spaces and stabilisation in homotopy type theory.")

#### homotopy

This directory contains the theory of Eilenberg-MacLane spaces, including their uniqueness.

Citation
--------

We copy here the citation for the original HoTT-Agda library.

```
@online{hott-in:agda,
  author={Guillaume Brunerie
    and Kuen-Bang {Hou (Favonia)}
    and Evan Cavallo
    and Tim Baumann
    and Eric Finster
    and Jesper Cockx
    and Christian Sattler
    and Chris Jeris
    and Michael Shulman
    and others},
  title={Homotopy Type Theory in {A}gda},
  url={https://github.com/HoTT/HoTT-Agda}
}
```

Names are roughly sorted by the amount of contributed code, with the founder Guillaume always staying on the
top.

License
-------
This work is released under [MIT license](https://opensource.org/licenses/MIT).
See [LICENSE.md](LICENSE.md).

Acknowledgments
---------------

This material was sponsored by the National Science Foundation under grant numbers CCF-1116703 and DMS-1638352;
Air Force Office of Scientific Research under grant numbers FA-95501210370 and FA-95501510053.
The views and conclusions contained in this document are those of the author and should not be
interpreted as representing the official policies, either expressed or implied, of any sponsoring
institution, the U.S. government or any other entity.
