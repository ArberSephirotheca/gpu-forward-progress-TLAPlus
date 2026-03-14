#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

SOURCE_ROOT="${SOURCE_ROOT:-/home/zheyuan/gpu-forward-progress-tests-suites/test_amber/intel_iris_xe}"
DEST_ROOT="${DEST_ROOT:-${PROJECT_ROOT}/artifact/amber_tests/intel_iris_xe_first100}"
LIMIT="${LIMIT:-100}"

readonly SUITES=(
    syn_branch_syn_rw
    syn_branch_syn_wr
    syn_branch_syn_ww
    syn_lock_step_wr
    syn_lock_step_rw
    syn_lock_step_ww
    syn_memory_converge_ra
    syn_subgroup_op_rw
    syn_subgroup_op_wr
    syn_subgroup_op_ww
)

fail() {
    echo "error: $*" >&2
    exit 1
}

copy_suite() {
    local suite="$1"
    local src_dir="${SOURCE_ROOT}/${suite}"
    local dst_dir="${DEST_ROOT}/${suite}"
    local count=0
    local variant_paths=()

    [[ -d "${src_dir}" ]] || fail "missing source suite: ${src_dir}"

    mkdir -p "${dst_dir}"
    cp "${src_dir}/reference.amber" "${dst_dir}/reference.amber"

    mapfile -t variant_paths < <(find "${src_dir}" -maxdepth 1 -type f -name 'variant_*.amber' | sort)

    if [[ "${#variant_paths[@]}" -lt "${LIMIT}" ]]; then
        fail "expected at least ${LIMIT} variants in ${src_dir}, found ${#variant_paths[@]}"
    fi

    for variant_path in "${variant_paths[@]:0:${LIMIT}}"; do
        cp "${variant_path}" "${dst_dir}/"
        count=$((count + 1))
    done

    if [[ "${count}" -ne "${LIMIT}" ]]; then
        fail "expected ${LIMIT} variants in ${src_dir}, copied ${count}"
    fi

    if [[ "${suite}" == "syn_subgroup_op_rw" ]]; then
        while IFS= read -r amber_file; do
            perl -0pi -e 'if (/(.*)atomicStore\((buf|checker)\[/s && $2 eq q(buf)) { s/(.*)atomicStore\(buf\[/\1atomicStore(checker[/s }' "${amber_file}"
        done < <(find "${dst_dir}" -maxdepth 1 -type f -name '*.amber' | sort)
    fi

    echo "copied ${suite}: reference + ${count} variants"
}

mkdir -p "${DEST_ROOT}"

for suite in "${SUITES[@]}"; do
    rm -rf "${DEST_ROOT:?}/${suite}"
    copy_suite "${suite}"
done
