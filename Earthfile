VERSION 0.6

ARG OUT=text

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
    RUN echo $OUT
    IF [ "$OUT" = "text" ]
        RUN tlc src/MCProgressModel > output.txt 2>&1 || true
    ELSE IF [ "$OUT" = "dot" ]
        RUN tlc src/MCProgressModel -dump dot,actionlabels,colorize output.dot 2>&1 || true 
    ELSE IF [ "$OUT" = "all" ]
        RUN tlc src/MCProgressModel -dump dot,actionlabels,colorize output.dot 2>&1 || true 
        RUN tlc src/MCProgressModel > output.txt 2>&1 || true
    ELSE
        RUN echo "Invalid output format"
    END
    SAVE ARTIFACT output.* AS LOCAL ./build/