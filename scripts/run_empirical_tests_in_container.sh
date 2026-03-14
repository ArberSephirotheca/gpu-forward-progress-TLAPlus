#!/usr/bin/env bash
set -euo pipefail

SUITE_ROOT="${SUITE_ROOT:-/workdir/empirical_tests/evaluation_tests}"
OUTPUT_DIR="${OUTPUT_DIR:-/output/empirical_evaluation_results}"
TIMEOUT_SECS="${TIMEOUT_SECS:-30}"
AMBER_BIN="${AMBER_BIN:-/usr/local/bin/amber}"

fail() {
    echo "error: $*" >&2
    exit 1
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

    test_name="$(basename "${amber_file}")"
    log_file="${suite_out}/${test_name}.log"

    if timeout -k 5 "${TIMEOUT_SECS}" "${AMBER_BIN}" "${amber_file}" > "${log_file}" 2>&1; then
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

main() {
    [[ -x "${AMBER_BIN}" ]] || fail "amber binary not found: ${AMBER_BIN}"
    [[ -d "${SUITE_ROOT}" ]] || fail "suite root not found: ${SUITE_ROOT}"

    mkdir -p "${OUTPUT_DIR}"
    : > "${OUTPUT_DIR}/summary.csv"
    : > "${OUTPUT_DIR}/all_results.csv"
    printf 'suite,passed,failed,timed_out\n' >> "${OUTPUT_DIR}/summary.csv"
    printf 'suite,test_name,status,exit_code\n' >> "${OUTPUT_DIR}/all_results.csv"

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

main "$@"
