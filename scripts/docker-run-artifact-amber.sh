#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

IMAGE_NAME="${IMAGE_NAME:-gpu-subgroup-artifact-amber:latest}"
DOCKER_NETWORK="${DOCKER_NETWORK:-host}"
DOCKERFILE_PATH="${DOCKERFILE_PATH:-${PROJECT_ROOT}/Dockerfile.artifact-tests}"
OUTPUT_SUBDIR="${OUTPUT_SUBDIR:-artifact_amber_results}"
TIMEOUT_SECS="${TIMEOUT_SECS:-30}"
SKIP_BUILD="FALSE"

usage() {
    cat <<'EOF'
Usage:
  scripts/docker-run-artifact-amber.sh

Options:
  --skip-build         Reuse an existing image instead of rebuilding.
  --image <name>       Override image name/tag.
  --network <name>     Docker network mode/name (default: host).
  --timeout <secs>     Per-test timeout passed into the container.
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
        -h|--help)
            usage
            exit 0
            ;;
        *)
            fail "unknown option: $1"
            ;;
    esac
done

[[ -d "${PROJECT_ROOT}/artifact/amber_tests/intel_iris_xe_first100" ]] || \
    fail "missing artifact/amber_tests/intel_iris_xe_first100; run scripts/extract_artifact_amber_subset.sh first"

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
    -e SUITE_ROOT="/workdir/artifact/amber_tests/intel_iris_xe_first100" \
    -e TIMEOUT_SECS="${TIMEOUT_SECS}" \
    -v "${PROJECT_ROOT}:/workdir:ro" \
    -v "${PROJECT_ROOT}/build:/output" \
    "${IMAGE_NAME}"
