# gpu-subgroup-semantics-TLAPlus

This artifact accompanies *SIMT-Step Execution: A Flexible Operational Semantics for GPU Subgroup Behavior*.
It packages:

- an executable TLA+ model under [`forward-progress/validation/`](forward-progress/validation)
- a SPIR-V-to-TLA+ compiler under [`Homunculus/`](Homunculus)
- example shaders under [`example_shader_program/`](example_shader_program)
- empirical Amber suites under [`empirical_tests/`](empirical_tests)

This README is organized in the two parts expected by artifact evaluation:

1. Part I. Getting Started Guide
2. Part II. Step-by-Step Instructions

Generated outputs are written under `build/`. The `build/` directory is not checked into git, so the files described below are generated on demand rather than shipped as precomputed logs.

## Part I. Getting Started Guide

A reviewer who follows it should be able to confirm that the artifact can:

- translate a shader into a program-specific TLA+ model
- run TLC on the generated model
- expose the main files that correspond to the paper's operational semantics

### 1. Environment and Setup
Required for the basic semantics pipeline:

- [Docker Engine](https://docs.docker.com/engine/install/)
- [Git](https://git-scm.com/book/en/v2/Getting-Started-Installing-Git)
- Bash shell

Additional requirements for the empirical GPU experiments in Part II:
- a Linux machine where a Docker container can access a Vulkan-capable GPU
- the documented host setups in this artifact are:
  - Intel/AMD via `/dev/dri/renderD*`
  - NVIDIA via `nvidia-smi` and NVIDIA Container Toolkit configured for Docker

Support boundary:

- The main TLA+ pipeline in [`scripts/docker-run-tlaplus.sh`](scripts/docker-run-tlaplus.sh) only requires Docker.
- The empirical Amber pipeline in [`scripts/docker-run-empirical-tests.sh`](scripts/docker-run-empirical-tests.sh) is documented only for Linux GPU hosts.
- macOS, Windows, and WSL are not documented for the empirical GPU runs.
- Podman is not the documented or validated path for this artifact.

Before continuing, unpack the artifact or clone the repository, then enter the repository root.

### 2. Verify Docker

Run:

```bash
docker version
docker run hello-world
```

If Docker reports `permission denied while trying to connect to the Docker daemon socket`, either:

- rerun the helper scripts with `sudo`, or
- configure Docker for non-root use and then re-login before retrying

The helper scripts now fail early with a clearer message when Docker is installed but the daemon socket is not accessible to the current user.

### 3. Test

Run one end-to-end semantics example:

```bash
scripts/docker-run-tlaplus.sh --input example_shader_program/synchronization/cm.comp --out text
```

What this command does:

- builds the main Docker image if needed
- compiles the example shader to SPIR-V
- translates the SPIR-V program into a program-specific TLA+ module
- runs TLC on the generated model

Expected generated outputs under `build/`:

- `MCProgram.tla`
- `output.txt`
- `spirv-asm.txt`
- `example_shader_program/synchronization/cm.comp.spv`

Success criteria:

- the command finishes without a Docker error
- `build/MCProgram.tla` exists
- `build/output.txt` exists and contains TLC output

Notes:

- The first run may take a while because it builds the Docker image.
- `build/MCProgram.tla` is overwritten on each new pipeline run.

### 4. What to Inspect After the Test

The quickest files to inspect are:

- `build/MCProgram.tla`
  - the generated, program-specific TLA+ module for the shader you just ran
- [`forward-progress/validation/MCThreads.tla`](forward-progress/validation/MCThreads.tla)
  - the hand-written instruction semantics
- [`forward-progress/validation/MCProgressModel.tla`](forward-progress/validation/MCProgressModel.tla)
  - the model-checking harness that defines `Init` and `Next`
- `build/output.txt`
  - the TLC run log for the generated model

At this point, a reviewer has completed the basic artifact validation path.

### 5. Optional GPU Test

If you have a supported Linux GPU environment and want a quick artifact-level experiment after the basic  test, run the evaluator-sized empirical subset:

```bash
scripts/docker-run-empirical-tests.sh
```

Expected runtime:

- about `5-8` minutes with a prebuilt image
- about `12-16` minutes on the first run if the empirical Docker image must be built

Expected generated outputs under `build/empirical_evaluation_results/`:

- `summary.md`
- `summary.csv`
- `all_results.csv`
- `vulkaninfo_summary.txt`
- `<suite>/*.log`

Warnings that are usually safe to ignore in this headless/containerized setting:

- `'DISPLAY' environment variable not set... skipping surface info`
- `error: XDG_RUNTIME_DIR not set in the environment.`
- `terminator_CreateInstance: Failed to CreateInstance in ICD 0. Skipping ICD.`
- `llvmpipe` appearing in `vulkaninfo --summary` alongside a real hardware GPU

These warnings are not fatal by themselves. What matters is that:

- the run produces the output files above
- `vulkaninfo_summary.txt` lists a real hardware GPU
- suite logs are written under `build/empirical_evaluation_results/`

## Part II. Step-by-Step Instructions

This part is for evaluators and researchers who want to reproduce the artifact's experiments, connect them back to the paper, and inspect the implementation in more depth.

### 1. Claims Supported by This Artifact

The artifact supports the following paper claims by providing executable models, included tests, and reproduction scripts.

| Claim supported by the artifact | Paper connection | How to evaluate it |
|---|---|---|
| The four direct SIMT-Step models implemented in the artifact can be executed as TLA+ semantics and checked with TLC. | Sec. 4, Sec. 5, and Table 1 | Run [`scripts/docker-run-tlaplus.sh`](scripts/docker-run-tlaplus.sh) on one of the shaders in [`example_shader_program/synchronization/`](example_shader_program/synchronization), then inspect `build/MCProgram.tla` and `build/output.txt`. |
| Dynamic blocks, branching, merge handling, and reconvergence are represented explicitly in the artifact. | Sec. 3 and Sec. 4 | Inspect [`forward-progress/validation/MCProgram.tla`](forward-progress/validation/MCProgram.tla) and [`forward-progress/validation/MCThreads.tla`](forward-progress/validation/MCThreads.tla), then compare the generated `build/MCProgram.tla` after running `cm.comp` or `scf.comp`. |
| The direct models CM, SM, SCF, and SSO from Table 1 are encoded in the executable model and exercised by included example shaders. | Sec. 4, Sec. 5, and Table 1 | Run the four example shaders in [`example_shader_program/synchronization/`](example_shader_program/synchronization) and inspect the generated `build/MCProgram.tla` for each run. |
| The artifact provides an end-to-end toolchain from GLSL input to SPIR-V, to generated TLA+, to TLC output. | Sec. 5.1 and Fig. 12 | Inspect [`scripts/docker-run-tlaplus.sh`](scripts/docker-run-tlaplus.sh), [`Dockerfile`](Dockerfile), and [`Homunculus/`](Homunculus), then reproduce the pipeline with `scripts/docker-run-tlaplus.sh`. |
| The bundled Amber suites exercise the paper-aligned direct-model test families for CM, SM, SCF, and SSO. | Sec. 5.2, Fig. 2, Fig. 3, and Fig. 9 | Run [`scripts/docker-run-empirical-tests.sh`](scripts/docker-run-empirical-tests.sh) for the evaluation subset or `--full` for the larger campaign, then inspect the generated summaries and logs in `build/`. |

### 2. Claims Not Supported by This Artifact

The artifact does not by itself establish the following broader paper claims:

- The full cross-device empirical conclusion from Sec. 6.2.
  - The paper's study spans nine GPUs from seven vendors and totals over 700 hours of testing.
  - Running the artifact on a single evaluator machine provides partial reproduction of that evidence, not the full study.
- The weaker `Spec` and `Symb` models from Table 1.
  - Sec. 5 states that the tool suite focuses on the first four direct models.
- Broad empirical portability across all OSes and GPU environments.
  - The documented empirical path is Linux-only and requires a Vulkan-capable GPU environment.

### 3. Reproduce the Executable Semantics Pipeline

#### 3.1 Single Example

Run:

```bash
scripts/docker-run-tlaplus.sh --input example_shader_program/synchronization/cm.comp --out text
```

This is the smallest end-to-end reproduction of the artifact's main semantics pipeline.

Generated outputs:

- `build/MCProgram.tla`
- `build/output.txt`
- `build/spirv-asm.txt`
- `build/example_shader_program/synchronization/cm.comp.spv`

Interpretation:

- `build/MCProgram.tla` is the generated TLA+ module specialized to the input shader.
- `build/output.txt` is TLC's log for that generated model.

#### 3.2 Compare the Four Synchronization Models

The repository includes one example shader for each model in the paper:

| Shader | Paper connection | Behavior to inspect |
|---|---|---|
| `example_shader_program/synchronization/cm.comp` | CM / Fig. 3 | collective memory behavior |
| `example_shader_program/synchronization/sm.comp` | SM / Fig. 2 | synchronous memory behavior |
| `example_shader_program/synchronization/scf.comp` | SCF / Fig. 9 without subgroup op | synchronous control-flow behavior |
| `example_shader_program/synchronization/sso.comp` | SSO / Fig. 9 with subgroup op | subgroup-operation synchronization behavior |

Run all four:

```bash
for model in cm sm scf sso; do
  scripts/docker-run-tlaplus.sh --input "example_shader_program/synchronization/${model}.comp" --out text
done
```

If you want the TLC graph dump as well, use:

```bash
scripts/docker-run-tlaplus.sh --input example_shader_program/synchronization/cm.comp --out dot
```

or:

```bash
scripts/docker-run-tlaplus.sh --input example_shader_program/synchronization/cm.comp --out all
```

Additional generated outputs for `dot` or `all`:

- `build/output.dot`

### 4. Reproduce the Empirical Amber Evaluation Subset

The paper-aligned Amber suites live under [`empirical_tests/`](empirical_tests).
The evaluator-sized subset is in [`empirical_tests/evaluation_tests/`](empirical_tests/evaluation_tests).

Before running the empirical suites, verify that the host and Docker setup expose a real Vulkan-capable GPU.
The host-side checks below help identify which supported Linux path the launcher will use:

```bash
docker run hello-world
vulkaninfo --summary

# Typical Intel/AMD DRM path:
ls /dev/dri/renderD*

# Typical NVIDIA path:
nvidia-smi
```

If the NVIDIA path is detected but Docker is not yet configured to expose the GPU to containers, the helper script will report:

```text
error: GPU platform 'nvidia' requires Docker to be configured for NVIDIA Container Toolkit; run 'sudo nvidia-ctk runtime configure --runtime=docker' and restart Docker
```

In that case, run:

```bash
sudo nvidia-ctk runtime configure --runtime=docker
sudo systemctl restart docker
```

The launcher defaults to `--gpu-platform auto`:

- it chooses `nvidia` when `nvidia-smi` works on the host
- otherwise it chooses `drm` when `/dev/dri/renderD*` is available

You can override the choice explicitly:

```bash
scripts/docker-run-empirical-tests.sh --gpu-platform drm
scripts/docker-run-empirical-tests.sh --gpu-platform nvidia
```

Suffix meanings:

- `ww`: write-write race pattern
- `rw`: read-write race pattern
- `wr`: write-read race pattern

| Suite | Paper mapping | Purpose |
|---|---|---|
| `cm_wr` | CM| Tests whether memory operations execute collectively. |
| `sm_ww`, `sm_rw`, `sm_wr` | SM | Tests whether memory operations execute synchronously. |
| `scf_ww`, `scf_rw`, `scf_wr` | SCF | Tests whether threads have synchronous control flow. |
| `sso_ww`, `sso_rw`, `sso_wr` | SSO | Tests whether subgroup operations synchronize with the associated control flow. |

Run:

```bash
scripts/docker-run-empirical-tests.sh
```

Expected runtime:

- about `5-8` minutes with a prebuilt image
- about `12-16` minutes if the empirical image must be built first

Generated outputs:

- `build/empirical_evaluation_results/summary.md`
- `build/empirical_evaluation_results/summary.csv`
- `build/empirical_evaluation_results/all_results.csv`
- `build/empirical_evaluation_results/vulkaninfo_summary.txt`
- `build/empirical_evaluation_results/gpu_platform.txt`
- `build/empirical_evaluation_results/<suite>/*.log`

How to interpret the output:

- `summary.md` gives the per-suite pass/fail counts.
- `all_results.csv` gives one row per Amber file.
- `vulkaninfo_summary.txt` records the Vulkan devices visible in the container.
- `<suite>/*.log` contains the raw Amber output for each test.

Important environment note:

- The empirical campaign is environment-sensitive.
- The repository documents Linux `drm` and Linux `nvidia` paths only.
- The bundled empirical campaign was curated from Intel Iris Xe runs, so exact outcomes may vary on AMD or NVIDIA hardware.

### 5. Reproduce the Full Empirical Campaign

The full empirical campaign is under [`empirical_tests/full_tests/`](empirical_tests/full_tests).

Run:

```bash
scripts/docker-run-empirical-tests.sh --full
```

Runtime note:

- this run may take **days**, depending on the GPU and host

Smaller input:

- if you want the same workflow on a manageable scale, use the evaluation subset from Section 4 instead

Generated outputs:

- `build/empirical_full_results/summary.md`
- `build/empirical_full_results/summary.csv`
- `build/empirical_full_results/all_results.csv`
- `build/empirical_full_results/<suite>/*.log`

### 6. Map the Artifact Back to the Paper

The main paper-to-artifact connections are:

- Dynamic blocks (Sec. 3).
  - `DynamicBlock` in [`forward-progress/validation/MCProgram.tla`](forward-progress/validation/MCProgram.tla) defines the record storing the SIS, thread sets, block label, identifier, merge stack, and child blocks.
  - `BranchUpdate` and `BranchConditionalUpdateSubgroup` in [`forward-progress/validation/MCProgram.tla`](forward-progress/validation/MCProgram.tla) evolve the dynamic execution graph when control flow splits and reconverges.
- Instruction classes (Sec. 4 and Table 1).
  - `IsCollectiveInstruction` and `IsSynchronousInstruction` in [`forward-progress/validation/MCProgram.tla`](forward-progress/validation/MCProgram.tla) encode the direct-model classification used by the executable semantics.
- Dynamic-block evolution (Sec. 4).
  - Independent branching is handled by `BranchUpdate`, `OpBranch`, and `OpBranchConditional`.
  - Collective control-flow entry and exit are handled by `BranchConditionalUpdateSubgroup`, `OpBranchCollective`, `OpBranchConditionalCollective`, and `OpLabelCollective`.
- Thread-level semantics (Sec. 4).
  - `ExecuteInstruction` in [`forward-progress/validation/MCThreads.tla`](forward-progress/validation/MCThreads.tla) dispatches to memory, collective control-flow, and subgroup-operation handlers.
- System-level specification (Sec. 4).
  - [`forward-progress/validation/MCProgressModel.tla`](forward-progress/validation/MCProgressModel.tla) assembles the program, threads, scheduler, `Init`, `Step`, and `Next` relations used by TLC.
- Initial state.
  - `InitProgram` in [`forward-progress/validation/MCProgram.tla`](forward-progress/validation/MCProgram.tla) expands to `InitDB /\ InitGPU /\ InitGlobalCounter`.
  - `InitThreads` in [`forward-progress/validation/MCThreads.tla`](forward-progress/validation/MCThreads.tla) initializes per-thread PCs and local state.
  - `InitScheduler` and `InitState` in [`forward-progress/validation/MCProgressModel.tla`](forward-progress/validation/MCProgressModel.tla) initialize the chosen scheduler (`HSA` or `OBE`) and model state.
- Transition relation.
  - `Step` and `Next` in [`forward-progress/validation/MCProgressModel.tla`](forward-progress/validation/MCProgressModel.tla) invoke `ExecuteInstruction` and `UpdateFairExecutionSet` to advance execution while enforcing the scheduler and fairness structure.
  - Instruction handlers in [`forward-progress/validation/MCThreads.tla`](forward-progress/validation/MCThreads.tla) perform the primed assignments, and branching handlers call back into [`forward-progress/validation/MCProgram.tla`](forward-progress/validation/MCProgram.tla) to evolve dynamic blocks.


### 7. Artifact Layout for Researchers

Key directories and files:

- [`scripts/docker-run-tlaplus.sh`](scripts/docker-run-tlaplus.sh)
  - user-facing wrapper for the main semantics pipeline and the in-container entrypoint used by the main Docker image
- [`scripts/docker-run-empirical-tests.sh`](scripts/docker-run-empirical-tests.sh)
  - user-facing wrapper for the empirical Amber campaign and the in-container entrypoint used by the empirical Docker image
- [`Homunculus/`](Homunculus)
  - SPIR-V frontend and TLA+ code generator
- [`forward-progress/validation/`](forward-progress/validation)
  - hand-authored TLA+ modules and model-checking configuration
- [`example_shader_program/`](example_shader_program)
  - example inputs
- [`empirical_tests/`](empirical_tests)
  - empirical Amber suites

## Appendix A. GLSL Frontend Extensions Used by the Artifact

The example shaders use small GLSL-side annotations that configure the TLA+ model.

### Scheduler

```glsl
#pragma scheduler(<scheduler name>)
```

Supported schedulers:

- `HSA`
- `OBE`

### Subgroup Size

```glsl
layout(tla_subgroup_size = <num>) in;
```

`<num>` must be a non-zero positive integer.

### Number of Workgroups

```glsl
layout(tla_num_workgroups = <num>) in;
```

`<num>` must be a non-zero positive integer.

### Synchronization Model

```glsl
layout(tla_synchronization_id = <id>) in;
```

| `id` | Label | Collective instructions | Synchronous instructions | Independent instructions |
|---|---|---|---|---|
| `1` | SSO | subgroup ops (`OpGroup*`) | none | all remaining instructions |
| `2` | SCF | subgroup ops plus control flow | none | others |
| `3` | SM | subgroup ops plus control flow | `OpAtomicLoad`, `OpAtomicStore`, `OpAtomicOr` | others |
| `4` | CM | subgroup ops plus control flow plus all memory ops | none | others |

## Appendix B. Supported SPIR-V Subset

Supported instructions:

- Variables and memory:
  - `OpVariable`, `OpLoad`, `OpStore`, `OpAtomicLoad`, `OpAtomicStore`
- Control flow:
  - `OpBranch`, `OpBranchConditional`, `OpSwitch`, `OpSelectionMerge`, `OpLoopMerge`, `OpLabel`, `OpReturn`
- Logic and comparisons:
  - `OpLogicalOr`, `OpLogicalAnd`, `OpLogicalEqual`, `OpLogicalNotEqual`, `OpLogicalNot`, `OpEqual`, `OpNotEqual`, `OpLess`, `OpLessOrEqual`, `OpGreater`, `OpGreaterOrEqual`
- Arithmetic and atomics:
  - `OpAdd`, `OpSub`, `OpMul`, `OpAtomicAdd`, `OpAtomicSub`, `OpAtomicExchange`, `OpAtomicCompareExchange`
- Subgroup and synchronization:
  - `OpGroupAll`, `OpGroupAny`, `OpGroupNonUniformAll`, `OpGroupNonUniformAny`, `OpControlBarrier`

Notes:
- Supported scalar types are:
  - `int`
  - `uint`
  - `bool`

## Appendix C. Model Limitations

- The executable semantics and bundled tests focus on the four direct SIMT-Step models: CM, SM, SCF, and SSO.
- The weaker `Spec` and `Symb` models discussed in Table 1 are not implemented in the artifact toolchain.
- The artifact supports the SPIR-V and GLSL subset needed by the included examples and tests; it is not intended as a complete SPIR-V implementation.
- The model uses sequentially consistent-style reasoning in the executable semantics, while the empirical Vulkan tests necessarily use the strongest portable Vulkan atomics available to Amber and GLSL.

## Reference

- https://lamport.azurewebsites.net/tla/safety-liveness.pdf
