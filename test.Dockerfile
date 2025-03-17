####################################################################################################
# Build Agda
####################################################################################################

ARG GHC_VERSION=9.4.7
FROM fossa/haskell-static-alpine:ghc-${GHC_VERSION} AS agda

WORKDIR /build/agda
# Agda 2.7.0.1
ARG AGDA_VERSION=a6fc20c27ae953149b53a8997ba4a1c8b17d628a
RUN \
  git init && \
  git remote add origin https://github.com/agda/agda.git && \
  git fetch --depth 1 origin "${AGDA_VERSION}" && \
  git checkout FETCH_HEAD

# We build Agda and place it in /dist along with its data files.
# We explicitly use v1-install because v2-install does not support --datadir and --bindir
# to relocate executables and data files yet.
RUN \
  mkdir -p /dist && \
  cabal update && \
  cabal v2-install alex happy-2.0.2 && \
  cabal v1-install --bindir=/dist --datadir=/dist --datasubdir=/dist/data --enable-executable-static

####################################################################################################
# Type-check Agda files
####################################################################################################

FROM alpine AS hottagda

COPY ["HoTT-Agda", "/build/HoTT-Agda"]
COPY ["Two-groups", "/build/Two-groups"]

FROM alpine

COPY --from=agda /dist /dist
COPY --from=hottagda /build /build

RUN echo "/build/HoTT-Agda/hott-core.agda-lib" >> /dist/libraries
RUN echo "/build/Two-groups/two-group.agda-lib" >> /dist/libraries

WORKDIR /build/Two-groups
RUN /dist/agda --library-file=/dist/libraries ./Bicats/Premag-issue.agda