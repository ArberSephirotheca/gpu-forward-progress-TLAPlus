#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

IMAGE_NAME="${IMAGE_NAME:-gpu-subgroup-semantics-tlaplus:latest}"
DOCKER_NETWORK="${DOCKER_NETWORK:-host}"
OUT="${OUT:-text}"
INPUT="${INPUT:-}"
LITMUS_TESTS="${LITMUS_TESTS:-FALSE}"
MEMORY_MODEL="${MEMORY_MODEL:-RA}"
SKIP_BUILD="FALSE"
CONTAINER_MODE="FALSE"

WORKDIR="${WORKDIR:-/workdir}"
OUTPUT_DIR="${OUTPUT_DIR:-/output}"

readonly GLSLANG_BIN="glslang/build/install/bin/glslang"
readonly SPIRV_DIS_BIN="glslang/build/install/bin/spirv-dis"
readonly SPIRV_AS_BIN="glslang/build/install/bin/spirv-as"
readonly HOMUNCULUS_BIN="Homunculus/target/release/homunculus"
readonly MC_PROGRAM_PATH="forward-progress/validation/MCProgram.tla"
readonly MC_MODEL_PATH="forward-progress/validation/MCProgressModel"

usage() {
    cat <<'EOF'
Usage:
  scripts/docker-run-tlaplus.sh --input <shader.comp> --out <text|dot|all|fuzz> [--memory-model <ra|plain>]
  scripts/docker-run-tlaplus.sh --litmus-tests [--memory-model <ra|plain>]

Options:
  --input <path>      Input shader path relative to repository root.
  --out <format>      Output mode: text, dot, all, fuzz. Default: text.
  --litmus-tests      Run litmus test mode (requires ./litmus_tests).
  --memory-model <m>  Memory model: ra or plain. Default: ra.
  --skip-build        Skip docker image rebuild and reuse existing image.
  --image <name>      Override image name/tag.
  --network <name>    Docker network mode/name (default: host).
EOF
}

fail() {
    echo "error: $*" >&2
    exit 1
}

require_docker_access() {
    command -v docker >/dev/null 2>&1 || fail "docker CLI not found; install Docker Engine first"

    local err
    if err="$(docker version 2>&1 >/dev/null)"; then
        return
    fi

    if grep -qi "permission denied while trying to connect to the Docker daemon socket" <<<"${err}"; then
        local socket="/var/run/docker.sock"
        local socket_meta="unknown ownership"
        if [[ -S "${socket}" ]]; then
            socket_meta="$(stat -c '%U:%G %a' "${socket}" 2>/dev/null || printf 'unknown ownership')"
        fi
        fail "docker is installed but the daemon socket is not accessible to your user. ${socket} is ${socket_meta}. If 'sudo docker version' works, either rerun with sudo or configure Docker for non-root use (typically create/use the 'docker' group, add your user, then log out/in) before retrying"
    fi

    err="${err//$'\n'/ }"
    fail "docker is installed but the daemon is not reachable. Run 'docker version' and 'docker run hello-world' manually to confirm the host setup. Details: ${err}"
}

copy_file_to_output() {
    local src="$1"
    local rel_dst="${2:-$1}"
    mkdir -p "${OUTPUT_DIR}/$(dirname "${rel_dst}")"
    cp -f "${src}" "${OUTPUT_DIR}/${rel_dst}"
}

copy_glob_to_output() {
    local pattern="$1"
    shopt -s nullglob
    local files=(${pattern})
    shopt -u nullglob
    for file in "${files[@]}"; do
        local rel="${file#./}"
        copy_file_to_output "${file}" "${rel}"
    done
}

normalize_memory_model() {
    case "${MEMORY_MODEL}" in
        RA|ra)
            MEMORY_MODEL="RA"
            ;;
        Plain|plain)
            MEMORY_MODEL="Plain"
            ;;
        *)
            fail "unsupported --memory-model value: ${MEMORY_MODEL}"
            ;;
    esac
}

apply_memory_model() {
    local target="$1"
    [[ -f "${target}" ]] || fail "memory-model target not found: ${target}"
    grep -q '^MemoryModel ==' "${target}" || fail "MemoryModel configuration line not found in ${target}"
    sed -i "s/^MemoryModel == .*/MemoryModel == \"${MEMORY_MODEL}\"/" "${target}"
}

compile_shader() {
    [[ -n "${INPUT}" ]] || fail "no INPUT provided"
    [[ -f "${INPUT}" ]] || fail "input shader not found: ${INPUT}"

    "${GLSLANG_BIN}" -V --target-env spirv1.5 "${INPUT}" -o "${INPUT}.spv"
    copy_file_to_output "${INPUT}.spv" "${INPUT}.spv"

    "${SPIRV_DIS_BIN}" "${INPUT}.spv" > spirv-asm.txt 2>&1 || true
    copy_file_to_output "spirv-asm.txt" "spirv-asm.txt"
}

run_litmus_tests() {
    [[ -d litmus_tests ]] || fail "LITMUS_TESTS=TRUE requires ./litmus_tests"

    mkdir -p litmus_tests_spv litmus_tests_dis litmus_tests_result litmus_tests_mc_programs
    local mc_program_template="litmus_tests_mc_programs/MCProgram.template.tla"
    cp "${MC_PROGRAM_PATH}" "${mc_program_template}"

    shopt -s nullglob
    local tests=(litmus_tests/*.comp)
    shopt -u nullglob
    [[ ${#tests[@]} -gt 0 ]] || fail "no litmus tests found under litmus_tests/*.comp"

    for test_file in "${tests[@]}"; do
        local name
        name="$(basename "${test_file}" .comp)"

        cp "${mc_program_template}" "litmus_tests_mc_programs/${name}.tla"
        "${GLSLANG_BIN}" -V --target-env spirv1.5 "${test_file}" -o "litmus_tests_spv/${name}.spv"
        "${SPIRV_DIS_BIN}" "litmus_tests_spv/${name}.spv" > "litmus_tests_dis/${name}.txt"

        echo "Running test for ${name}"
        "${HOMUNCULUS_BIN}" compile "litmus_tests_dis/${name}.txt" "litmus_tests_mc_programs/${name}.tla"
        apply_memory_model "litmus_tests_mc_programs/${name}.tla"
        cp "litmus_tests_mc_programs/${name}.tla" "${MC_PROGRAM_PATH}"
        tlc "${MC_MODEL_PATH}" > "litmus_tests_result/${name}.txt" 2>&1 || true
    done

    copy_glob_to_output "litmus_tests_result/*.txt"
}

run_out_test() {
    local amber_test_dir="empirical_testing/test_amber"
    [[ -d "${amber_test_dir}" ]] || fail "OUT=test requires ${amber_test_dir}"

    cd "${amber_test_dir}"
    rm -rf ./results/*
    mkdir -p ../ALL_tests_tmp
    mkdir -p ../ALL_tests_tmp/2_thread_2_instruction
    mkdir -p ../ALL_tests_tmp/2_thread_3_instruction
    mkdir -p ../ALL_tests_tmp/2_thread_4_instruction
    mkdir -p ../ALL_tests_tmp/3_thread_3_instruction
    mkdir -p ../ALL_tests_tmp/3_thread_4_instruction

    cp ../ALL_tests_flat/2t_2i*/*.txt ../ALL_tests_tmp/2_thread_2_instruction/
    cp ../ALL_tests_flat/2t_3i*/*.txt ../ALL_tests_tmp/2_thread_3_instruction/
    cp ../ALL_tests_flat/2t_4i*/*.txt ../ALL_tests_tmp/2_thread_4_instruction/
    cp ../ALL_tests_flat/3t_3i*/*.txt ../ALL_tests_tmp/3_thread_3_instruction/
    cp ../ALL_tests_flat/3t_4i*/*.txt ../ALL_tests_tmp/3_thread_4_instruction/
    python3 amber_launch_tests.py
    rm -rf ../ALL_tests_tmp

    copy_glob_to_output "results/*"
}

run_main_pipeline() {
    compile_shader

    case "${OUT}" in
        text)
            "${HOMUNCULUS_BIN}" compile ./spirv-asm.txt
            apply_memory_model "${MC_PROGRAM_PATH}"
            JAVA_OPTS="-Xmx24G -XX:+UseParallelGC" tlc "${MC_MODEL_PATH}" -view -fpmem .25 -workers 20 2>&1 | tee output.txt || true
            copy_glob_to_output "output.*"
            ;;
        dot)
            "${HOMUNCULUS_BIN}" compile ./spirv-asm.txt
            apply_memory_model "${MC_PROGRAM_PATH}"
            JAVA_OPTS="-Xmx24G" tlc "${MC_MODEL_PATH}" -view -fpmem .50 -workers 20 -dump dot output.dot 2>&1 | tee output.txt || true
            copy_glob_to_output "output.*"
            ;;
        all)
            "${HOMUNCULUS_BIN}" compile ./spirv-asm.txt
            apply_memory_model "${MC_PROGRAM_PATH}"
            JAVA_OPTS="-Xmx32G" tlc "${MC_MODEL_PATH}" -view -fpmem .50 -workers 15 -maxSetSize 100 -dump dot output.dot 2>&1 | tee output.txt || true
            JAVA_OPTS="-Xmx32G" tlc "${MC_MODEL_PATH}" -view -fpmem .50 -workers 15 -maxSetSize 100 > output.txt 2>&1 || true
            copy_glob_to_output "output.*"
            ;;
        fuzz)
            "${HOMUNCULUS_BIN}" fuzz ./spirv-asm.txt
            "${SPIRV_AS_BIN}" --target-env spv1.5 -o fuzz.spv spirv-asm.txt.fuzz.txt
            spirv-cross --version 460 --no-es fuzz.spv --output fuzz.comp
            copy_file_to_output "spirv-asm.txt.fuzz.txt" "spirv-asm.txt.fuzz.txt"
            copy_file_to_output "fuzz.spv" "fuzz.spv"
            copy_file_to_output "fuzz.comp" "fuzz.comp"
            ;;
        *)
            fail "invalid output format: ${OUT}"
            ;;
    esac
}

run_in_container() {
    mkdir -p "${OUTPUT_DIR}"
    cd "${WORKDIR}"

    if [[ "${LITMUS_TESTS}" == "TRUE" ]]; then
        run_litmus_tests
    elif [[ "${OUT}" == "test" ]]; then
        run_out_test
    else
        run_main_pipeline
    fi

    if [[ -f "${MC_PROGRAM_PATH}" ]]; then
        copy_file_to_output "${MC_PROGRAM_PATH}" "MCProgram.tla"
    fi
}

run_on_host() {
    if [[ "${LITMUS_TESTS}" != "TRUE" && -z "${INPUT}" ]]; then
        fail "provide --input for standard modes, or use --litmus-tests"
    fi

    case "${OUT}" in
        text|dot|all|fuzz|test) ;;
        *) fail "unsupported --out value: ${OUT}" ;;
    esac

    if [[ -n "${INPUT}" && ! -f "${PROJECT_ROOT}/${INPUT}" ]]; then
        fail "input file not found: ${INPUT}"
    fi

    require_docker_access
    mkdir -p "${PROJECT_ROOT}/build"

    if [[ "${SKIP_BUILD}" != "TRUE" ]]; then
        docker build --network "${DOCKER_NETWORK}" -t "${IMAGE_NAME}" "${PROJECT_ROOT}"
    fi

    docker run --rm \
        --network "${DOCKER_NETWORK}" \
        -e OUT="${OUT}" \
        -e INPUT="${INPUT}" \
        -e LITMUS_TESTS="${LITMUS_TESTS}" \
        -e MEMORY_MODEL="${MEMORY_MODEL}" \
        -v "${PROJECT_ROOT}/build:/output" \
        "${IMAGE_NAME}"
}

main() {
    while [[ $# -gt 0 ]]; do
        case "$1" in
            --container-run)
                CONTAINER_MODE="TRUE"
                shift
                ;;
            --input)
                [[ $# -ge 2 ]] || fail "--input requires a value"
                INPUT="$2"
                shift 2
                ;;
            --out)
                [[ $# -ge 2 ]] || fail "--out requires a value"
                OUT="$2"
                shift 2
                ;;
            --litmus-tests)
                LITMUS_TESTS="TRUE"
                shift
                ;;
            --memory-model)
                [[ $# -ge 2 ]] || fail "--memory-model requires a value"
                MEMORY_MODEL="$2"
                shift 2
                ;;
            --skip-build)
                SKIP_BUILD="TRUE"
                shift
                ;;
            --image)
                [[ $# -ge 2 ]] || fail "--image requires a value"
                IMAGE_NAME="$2"
                shift 2
                ;;
            --network)
                [[ $# -ge 2 ]] || fail "--network requires a value"
                DOCKER_NETWORK="$2"
                shift 2
                ;;
            -h|--help)
                usage
                exit 0
                ;;
            *)
                fail "unknown option: $1"
                ;;
        esac
    done

    normalize_memory_model

    if [[ "${CONTAINER_MODE}" == "TRUE" ]]; then
        run_in_container
    else
        run_on_host
    fi
}

main "$@"
