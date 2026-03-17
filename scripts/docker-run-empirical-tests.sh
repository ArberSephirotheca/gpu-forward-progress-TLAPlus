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

while [[ $# -gt 0 ]]; do
    case "$1" in
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
