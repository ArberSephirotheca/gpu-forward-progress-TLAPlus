VERSION 0.6

tlaplusbuild-image:
    FROM openjdk:23-slim
    RUN apt-get update && apt-get install -y git bash sudo curl
    RUN git clone https://github.com/pmer/tla-bin.git
    WORKDIR /tla-bin
    RUN ./download_or_update_tla.sh
    RUN sudo ./install.sh
    SAVE IMAGE --push czyczy981/tlaplus:latest

tlaplus-image:
    FROM +tlaplusbuild-image
    WORKDIR /workdir
    COPY src src
    RUN tlc src/progress_model > output.txt 2>&1 || true
    SAVE ARTIFACT output.txt AS LOCAL ./build/
