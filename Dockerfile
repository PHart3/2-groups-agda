####################################################################################################
# Build Agda
####################################################################################################

ARG GHC_VERSION=9.8.2
FROM fossa/haskell-static-alpine:ghc-${GHC_VERSION}

ARG AGDA_VERSION=2.6.4.3
RUN \
  cabal update && \
  cabal install alex happy && \
  cabal install Agda-${AGDA_VERSION} --enable-executable-static

####################################################################################################
# Type-check Agda files
####################################################################################################

COPY . .

RUN echo "/HoTT-Agda/hott-core.agda-lib" >> /libraries
RUN echo "/HoTT-Agda/hott-theorems.agda-lib" >> /libraries
RUN echo "/Two-groups/two-group.agda-lib" >> /libraries 

WORKDIR /Two-groups
RUN agda --library-file=/libraries ./Grp-Type-biequiv/Biequiv-main.agda