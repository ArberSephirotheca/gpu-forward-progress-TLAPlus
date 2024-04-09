VERSION 0.6

tlaplusbuild-image:
    FROM ubuntu:22.04
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
    RUN pcal src/progress_model.tla > otuput.txt 2 & 1 || true
    SAVE ARTIFACT output.txt AS LOCAL ./build/

#     WORKDIR /workdir
#     COPY src src
#     RUN echo $model
#     IF [$model == '']
#         RUN cbmc src/main.c --unwind 50 --trace > output.txt 2>&1 || true
#     ELSE
#         RUN cbmc -D$model src/main.c --unwind 50 --trace > output.txt 2>&1 || true
#     END
# #--unwinding-assertions --cover assume 
#     SAVE ARTIFACT output.txt AS LOCAL ./build/