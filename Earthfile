VERSION 0.6

tlaplusbuild-image:
    FROM openjdk:23-slim
    RUN apt-get update && apt-get install -y git bash sudo curl graphviz clang cmake spirv-cross
    RUN curl https://sh.rustup.rs -sSf | sh -s -- -y
    ENV PATH="/root/.cargo/bin:${PATH}"
    RUN git config --global http.postBuffer 157286400
    RUN git clone https://github.com/pmer/tla-bin.git
    # RUN git clone https://github.com/KhronosGroup/glslang.git
    WORKDIR /tla-bin
    RUN ./download_or_update_tla.sh
    RUN sudo ./install.sh
    WORKDIR /workdir
    COPY glslang glslang
    WORKDIR /workdir/glslang
    RUN ./update_glslang_sources.py
    RUN mkdir -p build
    WORKDIR /workdir/glslang/build
    RUN cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX="$(pwd)/install" ..
    RUN make -j4 install
    SAVE IMAGE --push czyczy981/tlaplus:latest

tlaplus-image:
    ARG OUT=text
    ARG INPUT
    ARG LITMUS_TESTS=FALSE
    FROM +tlaplusbuild-image
    WORKDIR /workdir
    COPY forward-progress forward-progress
    COPY Homunculus Homunculus
    RUN CARGO_TARGET_DIR=Homunculus/target cargo build --release --manifest-path=Homunculus/Cargo.toml
    IF [ "$LITMUS_TESTS" = "TRUE" ]
        
        COPY litmus_tests litmus_tests
        RUN mkdir -p litmus_tests_spv
        RUN mkdir -p litmus_tests_dis
        RUN mkdir -p litmus_tests_result
        RUN mkdir -p litmus_tests_mc_programs
        FOR file IN $(ls litmus_tests/*.comp | sed 's|.*/||; s/\.comp$//')
            COPY forward-progress/validation/MCProgram.tla litmus_tests_mc_programs/$file.tla
        END
        FOR file IN $(ls litmus_tests/*.comp | sed 's|.*/||; s/\.comp$//')
            RUN glslang/build/install/bin/glslang -V --target-env vulkan1.3 "litmus_tests/${file}.comp" -o litmus_tests_spv/"${file}.spv"
        END
        FOR file IN $(ls litmus_tests_spv/*.spv | sed 's|.*/||; s/\.spv$//')
            RUN glslang/build/install/bin/spirv-dis "litmus_tests_spv/${file}.spv" > "litmus_tests_dis/${file}.txt"
        END
        RUN echo "Running forward progress tests"
        FOR file IN $(ls litmus_tests_dis/*.txt | sed 's|.*/||; s/\.txt$//')
            RUN echo "Running test for ${file}"
            RUN Homunculus/target/release/homunculus "litmus_tests_dis/${file}.txt" "litmus_tests_mc_programs/${file}.tla"
            RUN cp "litmus_tests_mc_programs/${file}.tla" forward-progress/validation/MCProgram.tla
            RUN tlc forward-progress/validation/MCProgressModel > "litmus_tests_result/${file}.txt" 2>&1 || true
        END
        SAVE ARTIFACT litmus_tests_result/*.txt AS LOCAL ./build/litmus_tests_result/
    ELSE IF [ "$INPUT" = "" ]
        RUN echo "No input file provided"
    ELSE
        COPY $INPUT $INPUT
        RUN glslang/build/install/bin/glslang -V --target-env vulkan1.3 $INPUT -o $INPUT.spv
        SAVE ARTIFACT $INPUT.spv AS LOCAL ./build/
        RUN glslang/build/install/bin/spirv-dis $INPUT.spv > spirv-asm.txt 2>&1 || true
        SAVE ARTIFACT spirv-asm.txt AS LOCAL ./build/
        IF [ "$OUT" = "text" ]
            RUN Homunculus/target/release/homunculus compile ./spirv-asm.txt 
            RUN JAVA_OPTS="-Xmx24G -XX:+UseParallelGC" tlc forward-progress/validation/MCProgressModel -view -fpmem .25 -workers 20 2>&1 | tee output.txt || true
            SAVE ARTIFACT output.* AS LOCAL ./build/
        ELSE IF [ "$OUT" = "dot" ]
            RUN Homunculus/target/release/homunculus compile ./spirv-asm.txt 
            RUN JAVA_OPTS="-Xmx24G" tlc forward-progress/validation/MCProgressModel -view -fpmem .50 -workers 20 -dump dot output.dot 2>&1 | tee output.txt || true 
            SAVE ARTIFACT output.* AS LOCAL ./build/
        ELSE IF [ "$OUT" = "all" ]
            RUN Homunculus/target/release/homunculus compile ./spirv-asm.txt 
            RUN JAVA_OPTS="-Xmx32G" tlc forward-progress/validation/MCProgressModel -view -fpmem .50 -workers 15 -maxSetSize 100 -dump dot output.dot 2>&1 | tee output.txt || true 
            RUN JAVA_OPTS="-Xmx32G" tlc forward-progress/validation/MCProgressModel -view -fpmem .50 -workers 15 -maxSetSize 100 > output.txt 2>&1 || true
            SAVE ARTIFACT output.* AS LOCAL ./build/
        ELSE IF [ "$OUT" = "fuzz" ]
            RUN Homunculus/target/release/homunculus fuzz ./spirv-asm.txt 
            # RUN spirv-cross --version 450 --no-es $INPUT.spv --output output.comp
            SAVE ARTIFACT *.txt AS LOCAL ./build/
        ELSE
            RUN echo "Invalid output format"
        END
    END    
    SAVE ARTIFACT forward-progress/validation/MCProgram.tla AS LOCAL ./build/
