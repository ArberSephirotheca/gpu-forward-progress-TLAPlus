#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

IMAGE_NAME="${IMAGE_NAME:-gpu-subgroup-empirical-tests:latest}"
DOCKER_NETWORK="${DOCKER_NETWORK:-host}"
DOCKERFILE_PATH="${DOCKERFILE_PATH:-${PROJECT_ROOT}/Dockerfile.empirical-tests}"
TEST_SET="${TEST_SET:-evaluation}"
OUTPUT_SUBDIR="${OUTPUT_SUBDIR:-}"
TIMEOUT_SECS="${TIMEOUT_SECS:-30}"
GPU_PLATFORM="${GPU_PLATFORM:-auto}"
SKIP_BUILD="FALSE"
CONTAINER_MODE="FALSE"

SUITE_ROOT="${SUITE_ROOT:-/workdir/empirical_tests/evaluation_tests}"
OUTPUT_DIR="${OUTPUT_DIR:-/output/empirical_evaluation_results}"
AMBER_BIN="${AMBER_BIN:-/usr/local/bin/amber}"
AMBER_SPIRV_TARGET="${AMBER_SPIRV_TARGET:-spv1.5}"
AMBER_DISABLE_VALIDATION="${AMBER_DISABLE_VALIDATION:-1}"

usage() {
    cat <<'EOF'
Usage:
  scripts/docker-run-empirical-tests.sh [--full] [--gpu-platform auto|drm|nvidia]

Options:
  --skip-build         Reuse an existing image instead of rebuilding.
  --image <name>       Override image name/tag.
  --network <name>     Docker network mode/name (default: host).
  --timeout <secs>     Per-test timeout passed into the container.
  --gpu-platform <p>   GPU attachment mode: auto, drm, or nvidia. Default: auto.
  --full               Run the full empirical suites instead of the evaluation subset.
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

detect_gpu_platform() {
    case "${GPU_PLATFORM}" in
        auto|drm|nvidia) ;;
        *) fail "unsupported --gpu-platform value: ${GPU_PLATFORM}" ;;
    esac

    if [[ "${GPU_PLATFORM}" != "auto" ]]; then
        printf '%s\n' "${GPU_PLATFORM}"
        return
    fi

    if command -v nvidia-smi >/dev/null 2>&1 && nvidia-smi -L >/dev/null 2>&1; then
        printf 'nvidia\n'
        return
    fi

    if compgen -G "/dev/dri/renderD*" >/dev/null || [[ -e /dev/dri ]]; then
        printf 'drm\n'
        return
    fi

    fail "no supported Linux GPU interface detected; expected either an NVIDIA host with nvidia-smi/NVIDIA Container Toolkit or a DRM render node under /dev/dri"
}

validate_gpu_platform() {
    local resolved="$1"
    case "${resolved}" in
        drm)
            if ! compgen -G "/dev/dri/renderD*" >/dev/null && [[ ! -e /dev/dri ]]; then
                fail "GPU platform 'drm' requires a Linux DRM render node such as /dev/dri/renderD128"
            fi
            ;;
        nvidia)
            command -v nvidia-smi >/dev/null 2>&1 || fail "GPU platform 'nvidia' requires nvidia-smi on the host"
            nvidia-smi -L >/dev/null 2>&1 || fail "GPU platform 'nvidia' requires a working NVIDIA driver on the host"
            command -v nvidia-ctk >/dev/null 2>&1 || fail "GPU platform 'nvidia' requires NVIDIA Container Toolkit (missing nvidia-ctk)"
            docker info --format '{{json .Runtimes}}' 2>/dev/null | grep -q '"nvidia"' \
                || fail "GPU platform 'nvidia' requires Docker to be configured for NVIDIA Container Toolkit; run 'sudo nvidia-ctk runtime configure --runtime=docker' and restart Docker"
            ;;
        *)
            fail "internal error: unsupported resolved GPU platform: ${resolved}"
            ;;
    esac
}

configure_vulkan_loader() {
    local icd

    case "${GPU_PLATFORM}" in
        nvidia)
            for icd in /etc/vulkan/icd.d/*nvidia*.json /usr/share/vulkan/icd.d/*nvidia*.json; do
                if [[ -f "${icd}" ]]; then
                    export VK_ICD_FILENAMES="${icd}"
                    return
                fi
            done
            ;;
    esac
}

run_suite() {
    local suite_dir="$1"
    local suite_name
    local suite_out
    local passed=0
    local failed=0
    local timed_out=0

    suite_name="$(basename "${suite_dir}")"
    suite_out="${OUTPUT_DIR}/${suite_name}"

    mkdir -p "${suite_out}"
    : > "${suite_out}/suite_results.csv"
    printf 'test_name,status,exit_code,log_path\n' >> "${suite_out}/suite_results.csv"

    if [[ -f "${suite_dir}/reference.amber" ]]; then
        run_test "${suite_name}" "${suite_dir}/reference.amber" "${suite_out}" passed failed timed_out
    fi

    while IFS= read -r amber_file; do
        run_test "${suite_name}" "${amber_file}" "${suite_out}" passed failed timed_out
    done < <(find "${suite_dir}" -maxdepth 1 -type f -name 'variant_*.amber' | sort)

    printf '%s,%s,%s,%s\n' "${suite_name}" "${passed}" "${failed}" "${timed_out}" >> "${OUTPUT_DIR}/summary.csv"
}

run_test() {
    local suite_name="$1"
    local amber_file="$2"
    local suite_out="$3"
    local -n passed_ref="$4"
    local -n failed_ref="$5"
    local -n timeout_ref="$6"
    local test_name
    local log_file
    local exit_code
    local status
    local -a amber_cmd

    test_name="$(basename "${amber_file}")"
    log_file="${suite_out}/${test_name}.log"
    amber_cmd=("${AMBER_BIN}")
    if [[ "${AMBER_DISABLE_VALIDATION}" != "0" ]]; then
        amber_cmd+=("-d")
    fi
    amber_cmd+=("-t" "${AMBER_SPIRV_TARGET}" "${amber_file}")

    if timeout -k 5 "${TIMEOUT_SECS}" "${amber_cmd[@]}" > "${log_file}" 2>&1; then
        exit_code=0
        status="PASS"
        passed_ref=$((passed_ref + 1))
    else
        exit_code=$?
        if [[ "${exit_code}" -eq 124 || "${exit_code}" -eq 137 ]]; then
            status="TIMEOUT"
            timeout_ref=$((timeout_ref + 1))
        else
            status="FAIL"
            failed_ref=$((failed_ref + 1))
        fi
    fi

    printf '%s,%s,%s,%s/%s.log\n' "${test_name}" "${status}" "${exit_code}" "${suite_name}" "${test_name}" >> "${suite_out}/suite_results.csv"
    printf '%s,%s,%s,%s\n' "${suite_name}" "${test_name}" "${status}" "${exit_code}" >> "${OUTPUT_DIR}/all_results.csv"
}

run_in_container() {
    [[ -x "${AMBER_BIN}" ]] || fail "amber binary not found: ${AMBER_BIN}"
    [[ -d "${SUITE_ROOT}" ]] || fail "suite root not found: ${SUITE_ROOT}"
    configure_vulkan_loader

    mkdir -p "${OUTPUT_DIR}"
    : > "${OUTPUT_DIR}/summary.csv"
    : > "${OUTPUT_DIR}/all_results.csv"
    printf 'suite,passed,failed,timed_out\n' >> "${OUTPUT_DIR}/summary.csv"
    printf 'suite,test_name,status,exit_code\n' >> "${OUTPUT_DIR}/all_results.csv"
    printf '%s\n' "${GPU_PLATFORM}" > "${OUTPUT_DIR}/gpu_platform.txt"
    printf '%s\n' "${VK_ICD_FILENAMES:-}" > "${OUTPUT_DIR}/vk_icd_filenames.txt"

    amber -h > "${OUTPUT_DIR}/amber_help.txt" 2>&1 || true
    vulkaninfo --summary > "${OUTPUT_DIR}/vulkaninfo_summary.txt" 2>&1 || true

    while IFS= read -r suite_dir; do
        run_suite "${suite_dir}"
    done < <(find "${SUITE_ROOT}" -mindepth 1 -maxdepth 1 -type d | sort)

    {
        echo "# Empirical Test Summary"
        echo
        echo "| Suite | Passed | Failed | Timed out |"
        echo "|---|---:|---:|---:|"
        tail -n +2 "${OUTPUT_DIR}/summary.csv" | while IFS=, read -r suite passed failed timed_out; do
            echo "| ${suite} | ${passed} | ${failed} | ${timed_out} |"
        done
    } > "${OUTPUT_DIR}/summary.md"
}

run_on_host() {
    case "${TEST_SET}" in
        evaluation)
            HOST_SUITE_ROOT="${PROJECT_ROOT}/empirical_tests/evaluation_tests"
            CONTAINER_SUITE_ROOT="/workdir/empirical_tests/evaluation_tests"
            OUTPUT_SUBDIR="${OUTPUT_SUBDIR:-empirical_evaluation_results}"
            ;;
        full)
            HOST_SUITE_ROOT="${PROJECT_ROOT}/empirical_tests/full_tests"
            CONTAINER_SUITE_ROOT="/workdir/empirical_tests/full_tests"
            OUTPUT_SUBDIR="${OUTPUT_SUBDIR:-empirical_full_results}"
            ;;
        *)
            fail "unsupported TEST_SET: ${TEST_SET}"
            ;;
    esac

    [[ -d "${HOST_SUITE_ROOT}" ]] || fail "missing suite root: ${HOST_SUITE_ROOT}"
    require_docker_access
    GPU_PLATFORM="$(detect_gpu_platform)"
    validate_gpu_platform "${GPU_PLATFORM}"

    mkdir -p "${PROJECT_ROOT}/build/${OUTPUT_SUBDIR}"

    if [[ "${SKIP_BUILD}" != "TRUE" ]]; then
        docker build \
            --network "${DOCKER_NETWORK}" \
            -f "${DOCKERFILE_PATH}" \
            -t "${IMAGE_NAME}" \
            "${PROJECT_ROOT}"
    fi

    DOCKER_RUN_ARGS=(
        --rm
        --network "${DOCKER_NETWORK}"
        -e OUTPUT_DIR="/output/${OUTPUT_SUBDIR}"
        -e SUITE_ROOT="${CONTAINER_SUITE_ROOT}"
        -e TIMEOUT_SECS="${TIMEOUT_SECS}"
        -e GPU_PLATFORM="${GPU_PLATFORM}"
        -v "${PROJECT_ROOT}:/workdir:ro"
        -v "${PROJECT_ROOT}/build:/output"
    )

    case "${GPU_PLATFORM}" in
        drm)
            DOCKER_RUN_ARGS+=(--device /dev/dri:/dev/dri)
            ;;
        nvidia)
            DOCKER_RUN_ARGS+=(
                --gpus all
                -e NVIDIA_VISIBLE_DEVICES=all
                -e NVIDIA_DRIVER_CAPABILITIES=graphics,utility
            )
            ;;
    esac

    docker run "${DOCKER_RUN_ARGS[@]}" "${IMAGE_NAME}"
}

main() {
    while [[ $# -gt 0 ]]; do
        case "$1" in
            --container-run)
                CONTAINER_MODE="TRUE"
                shift
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
            --timeout)
                [[ $# -ge 2 ]] || fail "--timeout requires a value"
                TIMEOUT_SECS="$2"
                shift 2
                ;;
            --gpu-platform)
                [[ $# -ge 2 ]] || fail "--gpu-platform requires a value"
                GPU_PLATFORM="$2"
                shift 2
                ;;
            --full)
                TEST_SET="full"
                shift
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

    if [[ "${CONTAINER_MODE}" == "TRUE" ]]; then
        run_in_container
    else
        run_on_host
    fi
}

main "$@"
