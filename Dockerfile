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

RUN echo "export PATH=/root/.local/bin:$PATH" >> /root/.bashrc

####################################################################################################
# Type-check Agda files
####################################################################################################

COPY . .

RUN mkdir -p /root/.agda
RUN echo "/HoTT-Agda/hott-core.agda-lib" >> /root/.agda/libraries
RUN echo "/HoTT-Agda/hott-theorems.agda-lib" >> /root/.agda/libraries
RUN echo "/Two-groups/two-group.agda-lib" >> /root/.agda/libraries 

WORKDIR /Two-groups
RUN source /root/.bashrc && agda --library-file=/root/.agda/libraries --ignore-interfaces ./Grp-Type-biequiv/Biequiv-main.agda