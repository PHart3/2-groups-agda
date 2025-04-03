## Overview

We construct a fully verified biequivalence between
  1. the (2,1)-category of coherent 2-groups
  2. the (2,1)-category of 2-truncated connected pointed types.
The code has been checked with Agda 2.6.4.3.

## Organization

- `HoTT-Agda/`

  A stripped down version of Andrew Swan's [HoTT-Agda](https://github.com/awswan/HoTT-Agda/tree/agda-2.6.1-compatible) branch,
  with many changes and additions motivated by our construction
  of the biequivalence.

  See `HoTT-Agda/README.md` for details and for the license of the work inside this directory.

- `Two-groups/`

  Our formalization of the biequivalence.

  See `Two-groups/README.md` for details and for the license of the work inside this directory.


## Type-checking with Docker

1. Build Docker image:

   ```bash
   docker build . -t 2group
   ```
2. Generate HTML files:

   ```bash
   mkdir -p ./html
   docker run --mount type=bind,source=./html,target=/Two-groups/html 2group
   ```

   This may take a few minutes. The HTML files will be under `html/`,
   and `html/Biequiv-main.agda.html` will be the entry point.

## Acknowledgement

This material is based upon work supported by the Air Force Office of Scientific Research under award number FA9550-21-1-0009.
Any opinions, findings, and conclusions or recommendations expressed in this material are those of the author(s) and do not
necessarily reflect the views of the United States Air Force.~