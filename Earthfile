VERSION 0.6

ARG OUT=text

ARG INPUT

tlaplusbuild-image:
    FROM openjdk:23-slim
    RUN apt-get update && apt-get install -y git bash sudo curl graphviz clang cmake
    RUN git clone https://github.com/pmer/tla-bin.git
    RUN git clone https://github.com/KhronosGroup/glslang.git
    WORKDIR /tla-bin
    RUN ./download_or_update_tla.sh
    RUN sudo ./install.sh
    WORKDIR /glslang
    RUN ./update_glslang_sources.py
    RUN mkdir -p build
    WORKDIR /glslang/build
    RUN cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX="$(pwd)/install" ..
    RUN make -j4 install
    SAVE IMAGE --push czyczy981/tlaplus:latest


tlaplus-image:
    FROM +tlaplusbuild-image
    WORKDIR /workdir
    COPY forward-progress forward-progress
    RUN echo $INPUT
    IF [ "$INPUT" = "" ]
        RUN echo "No input file provided"
    ELSE
        COPY $INPUT $INPUT
        RUN /glslang/build/install/bin/glslang -V $INPUT -o $INPUT.spv
        RUN /glslang/build/install/bin/spirv-dis $INPUT.spv > spirv-asm.txt 2>&1 || true
    END
    IF [ "$OUT" = "text" ]
        RUN tlc forward-progress/validation/MCProgressModel  > output.txt 2>&1 || true
    ELSE IF [ "$OUT" = "dot" ]
        RUN tlc forward-progress/validation/MCProgressModel -dump dot,actionlabels,colorize output.dot 2>&1 || true 
    ELSE IF [ "$OUT" = "all" ]
        RUN tlc forward-progress/validation/MCProgressModel  -dump dot,actionlabels,colorize output.dot 2>&1 || true 
        RUN tlc forward-progress/validation/MCProgressModel > output.txt 2>&1 || true
    ELSE
        RUN echo "Invalid output format"
    END
    SAVE ARTIFACT output.* AS LOCAL ./build/
    SAVE ARTIFACT spirv-asm.txt AS LOCAL ./build/