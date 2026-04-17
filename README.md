# gpu-subgroup-semantics-TLAPlus

This artifact accompanies *SIMT-Step Execution: A Flexible Operational Semantics for GPU Subgroup Behavior*.
It packages:

- an executable TLA+ model under [`forward-progress/validation/`](forward-progress/validation)
- a SPIR-V-to-TLA+ compiler under [`Homunculus/`](Homunculus)
- basic pipeline-check shaders under [`example_shader_program/`](example_shader_program)
- litmus shaders under [`litmus_tests/`](litmus_tests)
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

### 3. Basic Pipeline Check

Run one minimal end-to-end pipeline check:

```bash
scripts/docker-run-tlaplus.sh --input example_shader_program/synchronization/cm.comp --out text
```

What this command does:

- builds the main Docker image if needed
- compiles the input shader to SPIR-V
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

### 4. What to Inspect After the Basic Pipeline Check

The quickest useful inspection path is:

1. Confirm that the shader configuration reached the generated model.
   Open `build/MCProgram.tla` and check the top-level assignments:
   - `Scheduler == ...`
   - `Synchronization == "CM"` for the command above
   - `NumWorkGroups == ...`
   - `WorkGroupSize == ...`
   - `SubgroupSize == ...`

   These values should match the GLSL-side annotations in the shader and show that the frontend emitted a program-specific TLA+ instance rather than a fixed template.

2. Confirm that the frontend generated program content, not just parameters.
   In `build/MCProgram.tla`, inspect:
   - `ThreadInstructions == ...`
   - `ThreadArguments == ...`
   - `Blocks == ...`

   These definitions are the concrete thread instruction stream, operands, and control-flow graph extracted from the input shader.

3. Confirm where the generated program connects to the hand-written semantics.
   Cross-check the generated `build/MCProgram.tla` with:
   - [`forward-progress/validation/MCThreads.tla`](forward-progress/validation/MCThreads.tla), where `ExecuteInstruction` dispatches instruction handlers
   - [`forward-progress/validation/MCProgressModel.tla`](forward-progress/validation/MCProgressModel.tla), where `Init`, `Step`, and `Next` assemble the model checked by TLC

4. Confirm that TLC actually ran on the generated module.
   In `build/output.txt`, look for:
   - `Parsing file /workdir/forward-progress/validation/MCProgram.tla`
   - `Finished computing initial states`
   - a completed TLC exploration outcome

At this point, a reviewer has completed the basic pipeline-validation path.

### 5. Optional GPU Test

If you have a supported Linux GPU environment and want a quick artifact-level experiment after the basic pipeline check, run the evaluator-sized empirical subset:

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

The artifact supports the following paper claims by providing executable models, bundled litmus suites, orientation examples, and reproduction scripts.

| Claim supported by the artifact | Paper connection | How to evaluate it |
|---|---|---|
| The four direct SIMT-Step models implemented in the artifact can be executed as TLA+ semantics and checked with TLC. | Sec. 4, Sec. 5, and Table 1 | Run [`scripts/docker-run-tlaplus.sh --litmus-tests`](scripts/docker-run-tlaplus.sh) and inspect `build/litmus_tests_result/summary.txt` together with the per-test TLC logs under `build/litmus_tests_result/`. |
| Dynamic blocks, branching, merge handling, and reconvergence are represented explicitly in the artifact. | Sec. 3 and Sec. 4 | Inspect [`forward-progress/validation/MCProgram.tla`](forward-progress/validation/MCProgram.tla) and [`forward-progress/validation/MCThreads.tla`](forward-progress/validation/MCThreads.tla), then compare the generated `build/MCProgram.tla` after the basic pipeline check in Section 3. |
| The direct models CM, SM, SCF, and SSO from Table 1 are encoded in the executable model and exercised by the bundled litmus suite. | Sec. 4, Sec. 5, and Table 1 | Run [`scripts/docker-run-tlaplus.sh --litmus-tests`](scripts/docker-run-tlaplus.sh) on the shaders in [`litmus_tests/`](litmus_tests) and inspect `build/litmus_tests_result/summary.txt`. |
| The artifact provides an end-to-end toolchain from GLSL input to SPIR-V, to generated TLA+, to TLC output. | Sec. 5.1 and Fig. 12 | Inspect [`scripts/docker-run-tlaplus.sh`](scripts/docker-run-tlaplus.sh), [`Dockerfile`](Dockerfile), and [`Homunculus/`](Homunculus), then reproduce the basic pipeline check from Section 3. |
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

### 3. Basic Pipeline Check and Synchronization Examples

#### 3.1 Basic Pipeline Check

Run:

```bash
scripts/docker-run-tlaplus.sh --input example_shader_program/synchronization/cm.comp --out text
```

This is the smallest end-to-end reproduction of the artifact's main semantics pipeline.
It is the recommended getting-started path for confirming that the toolchain works on your machine.

Generated outputs:

- `build/MCProgram.tla`
- `build/output.txt`
- `build/spirv-asm.txt`
- `build/example_shader_program/synchronization/cm.comp.spv`

Interpretation:

- `build/MCProgram.tla` is the generated TLA+ module specialized to the input shader.
- `build/output.txt` is TLC's log for that generated model.

#### 3.2 Optional Synchronization Examples

The repository also includes one small orientation shader for each model in the paper:

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

#### 3.3 Inspection Checklist for Generated Outputs

The table below makes the manual inspection steps explicit.

| Claim to inspect | File | What to check |
|---|---|---|
| The shader annotations were propagated into the model instance. | `build/MCProgram.tla` | `Scheduler == ...`, `Synchronization == ...`, `NumWorkGroups == ...`, `WorkGroupSize == ...`, `SubgroupSize == ...` |
| The frontend generated concrete instructions and arguments for this shader. | `build/MCProgram.tla` | `ThreadInstructions == ...` and `ThreadArguments == ...` |
| The frontend generated a control-flow graph. | `build/MCProgram.tla` | `Blocks == ...` and `MergeBlocks == ...` |
| The selected synchronization model changes instruction classification as in Table 1. | [`forward-progress/validation/MCProgram.tla`](forward-progress/validation/MCProgram.tla) | `CollectiveInstructionSet`, `SynchronousInstructionSet`, `IsCollectiveInstruction`, and `IsSynchronousInstruction` |
| The handwritten operational semantics dispatch on those classifications. | [`forward-progress/validation/MCThreads.tla`](forward-progress/validation/MCThreads.tla) | `ExecuteInstruction` and the collective/synchronous variants of atomic and branch handlers |
| TLC checked the generated model instance. | `build/output.txt` | `Parsing file ... MCProgram.tla`, `Finished computing initial states`, and a completed TLC outcome |

For the four synchronization examples in Section 3.2, the quickest expected check is:

| Shader | Minimal expected inspection result |
|---|---|
| `cm.comp` | `Synchronization == "CM"` and memory operations are treated as collective by the model classification |
| `sm.comp` | `Synchronization == "SM"` and memory operations are treated as synchronous rather than collective |
| `scf.comp` | `Synchronization == "SCF"` and branch/control-flow instructions are collective while memory operations are not |
| `sso.comp` | `Synchronization == "SSO"` and only subgroup instructions are collective |

### 4. Reproduce the Paper Litmus Suite

The paper-facing TLA+ evaluation path is the bundled litmus suite under [`litmus_tests/`](litmus_tests).
This is the main TLA+ path corresponding to the litmus tests discussed in the paper.
Unlike the basic pipeline check in Section 3, this path runs the collection of litmus shaders and compares each TLC outcome against the expectation registered in the runner.

Run:

```bash
scripts/docker-run-tlaplus.sh --litmus-tests
```

Generated outputs:

- `build/litmus_tests_result/summary.txt`
- `build/litmus_tests_result/<test>.txt`

How to interpret the output:

- `summary.txt` records one line per litmus shader plus a final aggregate line.
- `PASS` means the observed TLC outcome matched an expected passing test.
- `XFAIL` means the observed TLC outcome matched an expected failing test.
- `FAIL` or `XPASS` means the observed outcome differed from the registered expectation, and the script exits non-zero.
- Each `<test>.txt` file contains the raw TLC log for that specific litmus shader.

If you want a suite that distinguishes the executable `Plain` and `RA` memory models, and your checkout includes the optional model-diff litmus suite, run:

```bash
scripts/docker-run-tlaplus.sh --litmus-tests --litmus-suite model-diff --memory-model plain
scripts/docker-run-tlaplus.sh --litmus-tests --litmus-suite model-diff --memory-model ra
```

### 5. Reproduce the Empirical Amber Evaluation Subset

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

Under the current RA-enabled executable semantics for the currently supported global/shared atomics:

- `scf_wr`, `sm_wr`, and `sso_wr` are peer-visibility witnesses and are expected to pass under `Plain` but fail under `RA`.
- `scf_ww`, `sm_ww`, and `sso_ww` are indexed two-address overwrite witnesses over a two-element storage-buffer array, and are also expected to pass under `Plain` but fail under `RA`.
- `cm_wr` remains a collective-uniformity check rather than an RA-distinguishing witness.

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

### 6. Reproduce the Full Empirical Campaign

The full empirical campaign is under [`empirical_tests/full_tests/`](empirical_tests/full_tests).

Run:

```bash
scripts/docker-run-empirical-tests.sh --full
```

Runtime note:

- this run may take **days**, depending on the GPU and host

Smaller input:

- if you want the same workflow on a manageable scale, use the evaluation subset from Section 5 instead

Generated outputs:

- `build/empirical_full_results/summary.md`
- `build/empirical_full_results/summary.csv`
- `build/empirical_full_results/all_results.csv`
- `build/empirical_full_results/<suite>/*.log`

### 7. Map the Artifact Back to the Paper

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


### 8. Artifact Layout and Pipeline for Researchers

If you want to modify or extend the artifact, the shortest useful mental model is:

1. Input shader.
   - Start from a GLSL compute shader under [`example_shader_program/`](example_shader_program) for a basic pipeline check or under [`litmus_tests/`](litmus_tests) for the paper-facing TLA+ evaluation path.
   - The shader carries TLA+-specific annotations such as `#pragma scheduler(...)` and `layout(tla_synchronization_id = ...) in;`.

2. Shader compilation and driver script.
   - [`scripts/docker-run-tlaplus.sh`](scripts/docker-run-tlaplus.sh) is the main user-facing entrypoint.
   - It invokes the modified `glslang` toolchain, emits SPIR-V, runs the Homunculus frontend, and then launches TLC.

3. SPIR-V frontend and code generation.
   - [`Homunculus/`](Homunculus) parses the SPIR-V plus the custom annotations and writes the generated `build/MCProgram.tla`.
   - This is where shader-specific facts such as `Synchronization`, `ThreadInstructions`, `ThreadArguments`, and `Blocks` are emitted.

4. Hand-written executable semantics.
   - [`forward-progress/validation/MCProgram.tla`](forward-progress/validation/MCProgram.tla) contains the dynamic-block data structures, instruction classification, and control-flow update logic.
   - [`forward-progress/validation/MCThreads.tla`](forward-progress/validation/MCThreads.tla) contains thread-level instruction handlers and the main `ExecuteInstruction` dispatcher.
   - [`forward-progress/validation/MCProgressModel.tla`](forward-progress/validation/MCProgressModel.tla) builds the top-level TLA+ model checked by TLC.

5. Generated outputs and experiment drivers.
   - `build/` holds generated SPIR-V, generated TLA+, TLC logs, and empirical summaries.
   - [`scripts/docker-run-empirical-tests.sh`](scripts/docker-run-empirical-tests.sh) is the user-facing entrypoint for the Amber campaign.
   - [`empirical_tests/`](empirical_tests) contains the evaluator-sized subset and the larger full campaign.

In practice, the most common modification paths are:

- Add or change a shader input:
  edit the GLSL file under [`example_shader_program/`](example_shader_program) for a basic pipeline check or under [`litmus_tests/`](litmus_tests) for the paper-facing litmus suite, rerun [`scripts/docker-run-tlaplus.sh`](scripts/docker-run-tlaplus.sh), and inspect the regenerated outputs.
- Change the executable semantics of an existing model:
  edit [`forward-progress/validation/MCProgram.tla`](forward-progress/validation/MCProgram.tla) and, if instruction behavior changes, [`forward-progress/validation/MCThreads.tla`](forward-progress/validation/MCThreads.tla).
- Add a new synchronization model:
  follow Appendix B below.

## Appendix A. GLSL Frontend Extensions Used by the Artifact

The shaders under [`example_shader_program/`](example_shader_program) and [`litmus_tests/`](litmus_tests) use small GLSL-side annotations that configure the TLA+ model.

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

## Appendix B. Extending the Artifact with Another Synchronization Model

This appendix is for readers who want to add a fifth direct model or modify how one of the current models classifies instructions.

The shortest safe workflow is:

1. Extend the frontend encoding of the model identifier.
   - The GLSL-side annotation is `layout(tla_synchronization_id = <id>) in;`.
   - Homunculus parses that identifier and currently rejects values larger than `4`.
   - Update the parser/checking logic under [`Homunculus/compiler/src/codegen/context.rs`](Homunculus/compiler/src/codegen/context.rs) so the new identifier is accepted.

2. Map the new identifier to a model label in the generated TLA+.
   - [`Homunculus/compiler/src/codegen/common.rs`](Homunculus/compiler/src/codegen/common.rs) maps the numeric identifier to the emitted `Synchronization == "..."` assignment.
   - Add the new numeric case there so generated `build/MCProgram.tla` files carry a stable label for the new model.

3. Decide how the new model classifies instructions.
   - [`forward-progress/validation/MCProgram.tla`](forward-progress/validation/MCProgram.tla) defines:
     - `CollectiveInstructionSet`
     - `SynchronousInstructionSet`
     - `IndependentInstructionSet`
     - `IsCollectiveInstruction`
     - `IsSynchronousInstruction`
   - For many model extensions, this is the main place that must change.
   - If the new model only reclassifies existing instructions, these definitions may be sufficient.

4. Update dynamic-block behavior if the new model changes collective control flow.
   - [`forward-progress/validation/MCProgram.tla`](forward-progress/validation/MCProgram.tla) also contains the dynamic-block machinery.
   - The key control-flow update operators are:
     - `BranchUpdate`
     - `BranchConditionalUpdateSubgroup`
   - If the new model changes when divergence, reconvergence, or subgroup-wide branching should be collective, inspect these operators carefully.

5. Update instruction dispatch if the new model needs new execution behavior.
   - [`forward-progress/validation/MCThreads.tla`](forward-progress/validation/MCThreads.tla) uses `ExecuteInstruction` to choose between collective, synchronous, and independent handlers.
   - For example, atomic instructions already have separate collective, synchronous, and independent code paths.
   - If the new model requires a genuinely new execution mode rather than a reclassification of existing modes, this file will need new handlers and new dispatch cases.

6. Regenerate and inspect a minimal example.
   - Add a small shader under [`example_shader_program/`](example_shader_program) that uses the new synchronization id.
   - Run [`scripts/docker-run-tlaplus.sh`](scripts/docker-run-tlaplus.sh) on that shader.
   - Confirm in `build/MCProgram.tla` that:
     - `Synchronization == "..."` uses the new label
     - the generated `ThreadInstructions`, `ThreadArguments`, and `Blocks` are sensible
     - the instruction classification in the hand-written modules matches the intended semantics

7. Add a regression test.
   - Add at least one minimal example or litmus-style shader that distinguishes the new model from the existing four.
   - Document the expected result in this README so future evaluators do not have to infer it from raw TLC output.

The minimum files to inspect for this extension path are therefore:

- [`Homunculus/compiler/src/codegen/context.rs`](Homunculus/compiler/src/codegen/context.rs)
- [`Homunculus/compiler/src/codegen/common.rs`](Homunculus/compiler/src/codegen/common.rs)
- [`forward-progress/validation/MCProgram.tla`](forward-progress/validation/MCProgram.tla)
- [`forward-progress/validation/MCThreads.tla`](forward-progress/validation/MCThreads.tla)
- [`forward-progress/validation/MCProgressModel.tla`](forward-progress/validation/MCProgressModel.tla)

## Appendix C. Supported SPIR-V Subset

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

## Appendix D. Model Limitations

- The executable semantics and bundled tests focus on the four direct SIMT-Step models: CM, SM, SCF, and SSO.
- The weaker `Spec` and `Symb` models discussed in Table 1 are not implemented in the artifact toolchain.
- The artifact supports the SPIR-V and GLSL subset needed by the included examples and tests; it is not intended as a complete SPIR-V implementation.
- The model uses sequentially consistent-style reasoning in the executable semantics, while the empirical Vulkan tests necessarily use the strongest portable Vulkan atomics available to Amber and GLSL.

## Reference

- https://lamport.azurewebsites.net/tla/safety-liveness.pdf
