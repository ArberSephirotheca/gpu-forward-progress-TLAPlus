VERSION 0.6

ARG out

tlaplusbuild-image:
    FROM openjdk:23-slim
    RUN apt-get update && apt-get install -y git bash sudo curl graphviz
    RUN git clone https://github.com/pmer/tla-bin.git
    WORKDIR /tla-bin
    RUN ./download_or_update_tla.sh
    RUN sudo ./install.sh
    SAVE IMAGE --push czyczy981/tlaplus:latest


tlaplus-image:
    FROM +tlaplusbuild-image
    WORKDIR /workdir
    COPY src src
    RUN echo $out
    RUN tlc src/progress_model_obe > output.txt 2>&1 || true
    SAVE ARTIFACT output.txt AS LOCAL ./build/

    # If you want to use the graphviz to generate the graph, you can use the following command
    # RUN tlc src/progress_model_obe -dump dot,actionlabels,colorize output.dot 2>&1 || true 
    # SAVE ARTIFACT output.dot AS LOCAL ./build/