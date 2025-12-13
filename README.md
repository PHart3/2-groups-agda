## Overview

- We construct a fully verified biadjoint biequivalence between
    1. the (2,1)-category of coherent 2-groups
    2. the (2,1)-category of 2-truncated connected pointed types.
    
  We also derive a verified equality between them by way of univalence.

- We mechanize the equivalence between the type of *n*-groups (i.e., pointed connected *n*-types) and
  that of Sính triples (where *n* > 1).

The code has been checked with Agda 2.6.4.3.

## Organization

The library has three main components, each component depending on the previous ones. It also has a fourth component
collecting the main theorems.

- `HoTT-Agda/`

  A stripped down version of Andrew Swan's [HoTT-Agda](https://github.com/awswan/HoTT-Agda/tree/agda-2.6.1-compatible) branch,
  with many changes and additions motivated by our construction
  of the biadjoint biequivalence and by the work on Sính triples.

  See `HoTT-Agda/README.md` for details and for the license of the work inside this directory.

- `Bicats/`

  A collection of basic notions and facts about (2,1)-categories, which we also call bicategories in this work.

  See `Bicats/README.md` for details and for the license of the work inside this directory.

- `Two-groups/`

  Our formalization of the biadjoint biequivalence and the induced equality.

  See `Two-groups/README.md` for details and for the license of the work inside this directory.

- `Sinh/`

  Our formalization of the equivalence between pointed connected *n*-types (*n* > 1) and Sính triples.

  See `Sinh/README.md` for details and for the license of the work inside this directory.

- `Final/`

  A single file containing the final biadjoint biequivalence and equality, 
  the Sính-triples equivalence along with a description of the group action produced by
  this equivalence, and the composite type equivalence between pointed connected 2-types
  and Sính triples.

  See `Final/README.md` for details and for the license of the work inside this directory.

## Type-checking

1. Build Docker image:

   ```bash
   docker build . -t 2group
   ```

2. Generate HTML files:

   ```bash
   mkdir -p ./html
   docker run --mount type=bind,source=./html,target=/Final/html 2group
   ```

   This will take several minutes. The HTML files will be under `html/`, and
   `html/Final-thms.agda.html` will be the entry point.

**Important:**

- We have included all of the `.agdai` files (in the various `_build` directories) in case you do
  not want to perform the intensive type-checking on your machine from scratch. Pass the flag
  `--ignore-interfaces` to `agda` on the command line if you want to type check a file from scratch.
  
- The Dockerfile sees the build artifacts, so pass the same flag to the RUN command in the Dockerfile
  to build everything from scratch. Beware that, in this situation, our machine uses as much as 28.7 GB
  of physical memory and takes over 8 hours to build the Docker image. (Our machine is a Linux with 16 GB
  of RAM and 100 GB of swap space.)

- If you do choose to check everything from scratch, we suggest you avoid the overhead of Docker even if
  you have lots of available RAM. We have found that type-checking directly on a macOS with an M1 chip is
  much faster (but still intensive). See `Final/README.md` for relevant details.

- Comment out the final two imports in `Final/Final-thms` to reduce the type-checking by over an hour.
  Doing so will check all relevant type equivalences but not the biadjoint biequivalence.

- Finally, we have included in this repo's root a zip file of the generated html files for all of the Agda code,
  which should let you navigate the codebase immediately without having to use Docker at all. You should consider
  `Final-thms.html` the entry point.
