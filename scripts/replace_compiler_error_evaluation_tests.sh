#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

RESULTS_ROOT="${RESULTS_ROOT:-${PROJECT_ROOT}/build/empirical_evaluation_results}"
SUITE_ROOT="${SUITE_ROOT:-${PROJECT_ROOT}/empirical_tests/evaluation_tests}"
FULL_ROOT="${FULL_ROOT:-${PROJECT_ROOT}/empirical_tests/full_tests}"
EXTERNAL_ROOT="${EXTERNAL_ROOT:-/home/zheyuan/gpu-forward-progress-tests-suites/test_amber/intel_iris_xe}"
MAPPING_OUT="${MAPPING_OUT:-${RESULTS_ROOT}/compiler_error_replacements.csv}"

[[ -d "${RESULTS_ROOT}" ]] || {
    echo "error: missing results root: ${RESULTS_ROOT}" >&2
    exit 1
}

[[ -d "${SUITE_ROOT}" ]] || {
    echo "error: missing suite root: ${SUITE_ROOT}" >&2
    exit 1
}

[[ -d "${FULL_ROOT}" ]] || {
    echo "error: missing full test root: ${FULL_ROOT}" >&2
    exit 1
}

[[ -d "${EXTERNAL_ROOT}" ]] || {
    echo "error: missing external result root: ${EXTERNAL_ROOT}" >&2
    exit 1
}

python3 - "${RESULTS_ROOT}" "${SUITE_ROOT}" "${FULL_ROOT}" "${EXTERNAL_ROOT}" "${MAPPING_OUT}" <<'PY'
from pathlib import Path
import csv
import shutil
import sys

results_root = Path(sys.argv[1])
suite_root = Path(sys.argv[2])
full_root = Path(sys.argv[3])
external_root = Path(sys.argv[4])
mapping_out = Path(sys.argv[5])

suite_map = {
    "cm_wr": "syn_memory_converge_ra",
    "scf_rw": "syn_branch_syn_rw",
    "scf_wr": "syn_branch_syn_wr",
    "scf_ww": "syn_branch_syn_ww",
    "sm_rw": "syn_lock_step_rw",
    "sm_wr": "syn_lock_step_wr",
    "sm_ww": "syn_lock_step_ww",
    "sso_rw": "syn_subgroup_op_rw",
    "sso_wr": "syn_subgroup_op_wr",
    "sso_ww": "syn_subgroup_op_ww",
}

compiler_error = (
    "Only l-values corresponding to shader block storage or shared variables "
    "can be used with atomic memory functions."
)
assertion_crash = (
    "spvIR.h:165: unsigned int spv::Instruction::getImmediateOperand(int) const: "
    "Assertion `!idOperand[op]' failed."
)


def variant_key(name: str) -> tuple[int, str]:
    if name.endswith(".amber"):
        name = name[:-6]
    if name == "reference":
        return (-1, name)
    if name.startswith("variant_"):
        return (int(name.split("_", 1)[1]), name)
    raise ValueError(f"unexpected test name: {name}")


def load_external_rows(ext_suite: str) -> tuple[dict[str, dict[str, list[str]]], set[str]]:
    suite_dir = external_root / ext_suite
    csv_paths = sorted(suite_dir.glob("*final_results-*.csv"))
    if not csv_paths:
        raise SystemExit(f"error: no final_results csv files found in {suite_dir}")

    rows: dict[str, dict[str, list[str]]] = {}
    compiler_marked: set[str] = set()
    for csv_path in csv_paths:
        label = csv_path.name.split("_final_results-", 1)[0]
        with csv_path.open(newline="") as f:
            reader = csv.reader(f)
            for row in reader:
                if not row or row[0] == "Test File Name":
                    continue
                test_name = row[0]
                if test_name == "Total failures:":
                    continue
                flags = row[1:]
                rows.setdefault(test_name, {})[label] = flags
                if "I" in flags:
                    compiler_marked.add(test_name)
    return rows, compiler_marked


replacements = []
for suite_dir in sorted(p for p in suite_root.iterdir() if p.is_dir()):
    suite = suite_dir.name
    ext_suite = suite_map.get(suite)
    if ext_suite is None:
        continue

    suite_results_csv = results_root / suite / "suite_results.csv"
    if not suite_results_csv.is_file():
        raise SystemExit(f"error: missing suite results csv: {suite_results_csv}")

    failing_targets = []
    with suite_results_csv.open(newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            target_path = suite_dir / row["test_name"]
            if not target_path.is_file():
                continue
            log_path = results_root / row["log_path"]
            text = log_path.read_text(errors="ignore") if log_path.is_file() else ""
            if (
                row.get("exit_code") == "134"
                or compiler_error in text
                or assertion_crash in text
            ):
                failing_targets.append(row["test_name"])

    if not failing_targets:
        continue

    external_rows, compiler_marked = load_external_rows(ext_suite)
    full_suite_dir = full_root / ext_suite
    if not full_suite_dir.is_dir():
        raise SystemExit(f"error: missing full suite dir: {full_suite_dir}")

    candidate_names = []
    for test_name in sorted(external_rows, key=variant_key):
        if test_name == "reference":
            continue
        if test_name in compiler_marked:
            continue
        if variant_key(test_name)[0] <= 99:
            continue
        full_test_path = full_suite_dir / f"{test_name}.amber"
        if not full_test_path.is_file():
            raise SystemExit(f"error: missing full test file: {full_test_path}")
        candidate_names.append(test_name)

    if len(candidate_names) < len(failing_targets):
        raise SystemExit(
            f"error: suite {suite} has {len(failing_targets)} targets but only "
            f"{len(candidate_names)} full-suite non-compiler-error candidates"
        )

    for target_name, source_name in zip(sorted(failing_targets, key=variant_key), candidate_names):
        target_path = suite_dir / target_name
        source_path = full_suite_dir / f"{source_name}.amber"
        shutil.copyfile(source_path, target_path)
        source_flags = external_rows[source_name]
        replacements.append(
            (
                suite,
                target_name,
                ext_suite,
                f"{source_name}.amber",
                "|".join(source_flags.get("simple", [])),
                "|".join(source_flags.get("iteration_based", [])),
            )
        )

mapping_out.parent.mkdir(parents=True, exist_ok=True)
with mapping_out.open("w", newline="") as f:
    writer = csv.writer(f)
    writer.writerow(
        [
            "suite",
            "replaced_test",
            "source_suite",
            "source_test",
            "simple_flags",
            "iteration_based_flags",
        ]
    )
    writer.writerows(replacements)

print(f"replaced {len(replacements)} compiler-error evaluation tests")
print(f"mapping written to {mapping_out}")
PY
