## Overview

We construct a fully verified biequivalence between
  1. the (2,1)-category of coherent 2-groups
  2. the (2,1)-category of 2-truncated connected pointed types.
We also provide an equality between them by way of univalence.

The code has been checked with Agda 2.6.4.3.

A preprint outlining our mechanization is located at [2Grp-biequiv-preprint.pdf](2Grp-biequiv-preprint.pdf).

## Organization

The library has three main components, each component depending on the previous ones. It also has a fourth component
collecting the main theorems.

- `HoTT-Agda/`

  A stripped down version of Andrew Swan's [HoTT-Agda](https://github.com/awswan/HoTT-Agda/tree/agda-2.6.1-compatible) branch,
  with many changes and additions motivated by our construction
  of the biequivalence.

  See `HoTT-Agda/README.md` for details and for the license of the work inside this directory.

- `Bicats/`

  A collection of basic notions and facts about (2,1)-categories, which we also call bicategories in this work.

  See `Bicats/README.md` for details and for the license of the work inside this directory.

- `Two-groups/`

  Our formalization of the biequivalence and the induced equality.

  See `Two-groups/README.md` for details and for the license of the work inside this directory.

- `Final/`

  A single file containing the final biequivalence and equality.

## Type-checking

We have successfully tested the following Docker container on Linux with 16 GB of RAM and
100 GB of swap space.

1. Build Docker image:

   ```bash
   docker build . -t 2group
   ```

   Our machine uses as much as 28.7 GB of physical memory and takes about 8 hours to build. 

2. Generate HTML files:

   ```bash
   mkdir -p ./html
   docker run --mount type=bind,source=./html,target=/Two-groups/html 2group
   ```

   This may take a few minutes. The HTML files will be under `html/`, and
   `html/Final-thms.agda.html` will be the entry point.

If you can avoid the overhead of Docker, please do so. Type-checking directly on a
MacOS with an M1 chip is much faster in our experience (see `Two-groups/README.md`).

## Acknowledgement

This material is based upon work supported by the Air Force Office of Scientific Research under award number FA9550-21-1-0009.
Any opinions, findings, and conclusions or recommendations expressed in this material are those of the author(s) and do not
necessarily reflect the views of the United States Air Force.