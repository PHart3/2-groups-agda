####################################################################################################
# Build Agda
####################################################################################################

ARG GHC_VERSION=9.8-slim
FROM haskell:${GHC_VERSION}

ARG AGDA_VERSION=2.6.4.3
RUN \
  cabal update && \
  cabal install alex happy && \
  cabal install Agda-${AGDA_VERSION}

####################################################################################################
# Type check Agda files and generate HTML files
####################################################################################################

COPY . .

RUN mkdir -p /root/.agda
RUN echo "/HoTT-Agda/hott-core.agda-lib" >> /root/.agda/libraries
RUN echo "/HoTT-Agda/hott-theorems.agda-lib" >> /root/.agda/libraries
RUN echo "/Two-groups/2Grps/2grphom.agda-lib" >> /root/.agda/libraries
RUN echo "/Two-groups/two-group.agda-lib" >> /root/.agda/libraries 
RUN echo "/Bicats/bicats.agda-lib" >> /root/.agda/libraries
RUN echo "/Final/final.agda-lib" >> /root/.agda/libraries
RUN echo "/Sinh/sinh.agda-lib" >> /root/.agda/libraries

WORKDIR /Final

# Delete --ignore-interfaces from the following command to check everything from scratch.
RUN agda --library-file=/root/.agda/libraries --ignore-interfaces ./Final-thms.agda

CMD ["agda", "--html", "--library-file=/root/.agda/libraries", "./Final-thms.agda"]
