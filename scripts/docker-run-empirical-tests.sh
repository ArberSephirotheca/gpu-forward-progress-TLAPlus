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
SKIP_BUILD="FALSE"

usage() {
    cat <<'EOF'
Usage:
  scripts/docker-run-empirical-tests.sh [--full]

Options:
  --skip-build         Reuse an existing image instead of rebuilding.
  --image <name>       Override image name/tag.
  --network <name>     Docker network mode/name (default: host).
  --timeout <secs>     Per-test timeout passed into the container.
  --full               Run the full empirical suites instead of the evaluation subset.
EOF
}

fail() {
    echo "error: $*" >&2
    exit 1
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

[[ -e /dev/dri ]] || fail "/dev/dri is not available on this host; GPU Vulkan tests cannot run in Docker"

mkdir -p "${PROJECT_ROOT}/build/${OUTPUT_SUBDIR}"

if [[ "${SKIP_BUILD}" != "TRUE" ]]; then
    docker build \
        --network "${DOCKER_NETWORK}" \
        -f "${DOCKERFILE_PATH}" \
        -t "${IMAGE_NAME}" \
        "${PROJECT_ROOT}"
fi

docker run --rm \
    --network "${DOCKER_NETWORK}" \
    --device /dev/dri:/dev/dri \
    -e OUTPUT_DIR="/output/${OUTPUT_SUBDIR}" \
    -e SUITE_ROOT="${CONTAINER_SUITE_ROOT}" \
    -e TIMEOUT_SECS="${TIMEOUT_SECS}" \
    -v "${PROJECT_ROOT}:/workdir:ro" \
    -v "${PROJECT_ROOT}/build:/output" \
    "${IMAGE_NAME}"
