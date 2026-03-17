# gpu-subgroup-semantics-TLAPlus

## Guide for Evaluators

This artifact accompanies *SIMT-Step Execution: A Flexible Operational Semantics for GPU Subgroup Behavior* and is meant to let PLDI evaluators inspect the executable TLA+ model that realises the paper’s operational rules.

### Suggested Evaluator Workflow

1. Run one end-to-end semantics example:
```bash
scripts/docker-run.sh --input example_shader_program/synchronization/cm.comp --out text
```
2. Run the evaluation subset:
```bash
scripts/docker-run-empirical-tests.sh
```
This runs `100` Amber tests total (`10` suites, each with `reference.amber` plus different variants). Expect about `5-8` minutes with a prebuilt image or about `12-16` minutes on the first run if Docker also rebuilds the image.
3. If you want the larger experiment, run the full empirical campaign. This may **take days**, depending on the GPU:
```bash
scripts/docker-run-empirical-tests.sh --full
```

- **Dynamic blocks (Sec. 3).** `DynamicBlock` in `forward-progress/validation/MCProgram.tla:307` stores the SIS, thread sets (`currentThreadSet`, `notExecuteSet`, `unknownSet`), block label (`labelIdx`), identifier (`id`), merge stack, and child blocks. The merge target is recovered on branching via `BranchUpdate` (`forward-progress/validation/MCProgram.tla:558`).
- **Instruction classes (Sec. 4/Tab.1).** The CM/SM/SCF/SSO partitions are encoded via `IsCollectiveInstruction` / `IsSynchronousInstruction` in `forward-progress/validation/MCProgram.tla:264-303`.
- **Dynamic-block evolution (Sec. 4).** Independent branching: `BranchUpdate` (`MCProgram.tla:554`), `OpBranch` (`MCThreads.tla:1590`), `OpBranchConditional` (`MCThreads.tla:1671`). Collective branching/labels: `BranchConditionalUpdateSubgroup` (`MCProgram.tla:798`), `OpBranchCollective` (`MCThreads.tla:1545`), `OpBranchConditionalCollective` (`MCThreads.tla:1619`), `OpLabelCollective` (`MCThreads.tla:1866`).
- **Thread-level semantics (Sec. 4).** `MCThreads.tla:1918-2047` contains `ExecuteInstruction`, which dispatches to memory, collective control flow, and subgroup operations.
- **System-level spec (Sec. 4).** `forward-progress/validation/MCProgressModel.tla` assembles the program, threads, and scheduler, defining `Init` and `Next` so TLC checks the same fairness/liveness properties discussed in the paper.
- **Initial state (`Init` in `MCProgressModel.tla`)**
  - `InitProgram` (`MCProgram.tla`) = `InitDB` ∧ `InitGPU`.
  - `InitThreads` (`MCThreads.tla`) set up per-thread PCs/states.
  - `InitScheduler`, `InitState` (`MCProgressModel.tla`) choose the scheduler (HSA/OBE) and initialize scheduler state.
- **Transition relation**
  - `Step` / `Next` (`MCProgressModel.tla`) call `ExecuteInstruction` (`MCThreads.tla`) and `UpdateFairExecutionSet` to advance one ready thread while enforcing fairness.
  - Instruction handlers in `MCThreads.tla` perform the primed assignments; when control flow branches they invoke `BranchUpdate`/`BranchConditionalUpdateSubgroup` from `MCProgram.tla` to evolve the dynamic blocks.


### Worked Example — Collective Control Flow

Consider the T–Label / G–Collective-UBranch rules for CM/SM/SCF:

1. `OpLabelCollective` (`MCThreads.tla:1866`) waits until all threads in the dynamic block are aligned, then bumps their PCs together—mirroring Step–Label.
2. `OpBranchCollective` (`MCThreads.tla:1545`) calls `BranchConditionalUpdateSubgroup` (`MCProgram.tla:798`) which (a) update the thread set in the child dynamic block, (b) pushes merge targets onto the merge stack, and (c) reuses existing children when reconverging at a merge block.

Evaluators who want to follow the execution end-to-end can run `scripts/docker-run.sh --input example_shader_program/synchronization/cm.comp --out text`, open the generated `build/MCProgram.tla`, and observe how the CFG emitted for that shader instantiates these operators.

## Pre-requisites
- [Docker](https://docs.docker.com/engine/install/)
- [Git](https://git-scm.com/book/en/v2/Getting-Started-Installing-Git)
- Bash shell

The helper scripts in this repository call the `docker` CLI directly. Podman may be adaptable by translating the raw container commands manually, but it is not the documented or validated path for this artifact.

## Get Started
Run the end-to-end pipeline and collect outputs in `build/` (the helper script builds the image automatically unless `--skip-build` is set):
```bash
scripts/docker-run.sh --input <glsl compute file> --out <format>
```

Equivalent raw Docker command (without helper script):
```bash
docker build -t gpu-subgroup-semantics-tlaplus .
docker run --rm \
  --network host \
  -e INPUT=<glsl compute file> \
  -e OUT=<format> \
  -v "$(pwd)/build:/output" \
  gpu-subgroup-semantics-tlaplus
```

If your environment blocks Docker bridge networking, use host networking:
```bash
scripts/docker-run.sh --network host --input <glsl compute file> --out <format>
```

## Empirical Amber Suites
The paper-aligned empirical tests live under [empirical_tests](/home/zheyuan/gpu-subgroup_semantics-TLAPlus/empirical_tests).

- Evaluation subset: [empirical_tests/evaluation_tests](/home/zheyuan/gpu-subgroup_semantics-TLAPlus/empirical_tests/evaluation_tests). This contains the 10 base suites (`10` Amber files per suite, `100` total), so evaluators can run the suite quickly.
- Full empirical suites: [empirical_tests/full_tests](/home/zheyuan/gpu-subgroup_semantics-TLAPlus/empirical_tests/full_tests). This contains the full 10-suite collection, with `10001` Amber files per suite, for evaluators who want the larger campaign.

Suffix meanings:
- `ww`: write-write race pattern
- `rw`: read-write race pattern
- `wr`: write-read race pattern

| Suite | Paper mapping | Purpose |
|------|---------------|---------|
| `cm_wr` | CM, Fig. 3 | Tests whether memory operations behave collectively across the subgroup. This is the only collective-memory base test. |
| `sm_ww`, `sm_rw`, `sm_wr` | SM, Fig. 2 without the subgroup operation | Tests whether plain memory operations remain synchronous inside a converged basic block. |
| `scf_ww`, `scf_rw`, `scf_wr` | SCF, Fig. 9 without subgroup operations | Tests whether branch/merge structure enforces synchronous control-flow progress. |
| `sso_ww`, `sso_rw`, `sso_wr` | SSO, Fig. 9 with subgroup operations included | Tests whether subgroup operations synchronize with the associated control-flow dependencies. |

## Dockerized Empirical Runs
The Docker runner builds [Dockerfile.empirical-tests](/home/zheyuan/gpu-subgroup_semantics-TLAPlus/Dockerfile.empirical-tests) and executes Amber across either the evaluation subset or the full empirical suites.

Supported Linux host modes for the empirical Amber runs:
- `drm`: Intel and most AMD Linux setups where the GPU is exposed through `/dev/dri/renderD*`
- `nvidia`: NVIDIA Linux setups using Docker `--gpus all` plus NVIDIA Container Toolkit

Documented evaluator environment:
- `x86_64` Linux host
- Ubuntu `22.04 LTS` or `24.04 LTS`
- Docker Engine
- for Intel/AMD: `/dev/dri/renderD*` available
- for NVIDIA: `nvidia-smi` works on the host and Docker GPU support is configured

Concrete support boundary:
- The empirical campaign bundled with the repository was curated from Intel Iris Xe runs.
- The launcher [docker-run-empirical-tests.sh](/home/zheyuan/gpu-subgroup_semantics-TLAPlus/scripts/docker-run-empirical-tests.sh) now supports both Linux DRM GPUs and NVIDIA GPUs on Linux.
- macOS, Windows, and WSL are not supported for the empirical Docker runs.
- The TLA+ pipeline in [docker-run.sh](/home/zheyuan/gpu-subgroup_semantics-TLAPlus/scripts/docker-run.sh) does not have this GPU/Vulkan requirement; this restriction applies only to [docker-run-empirical-tests.sh](/home/zheyuan/gpu-subgroup_semantics-TLAPlus/scripts/docker-run-empirical-tests.sh).

What "Vulkan-capable GPU driver" means in this artifact:
- The host can expose at least one Vulkan physical device to user space.
- On Intel/AMD, this normally means `/dev/dri/renderD*` exists and `vulkaninfo --summary` succeeds.
- On NVIDIA, this normally means `nvidia-smi` succeeds on the host, NVIDIA Container Toolkit is configured for Docker, and the container can start with `--gpus all`.
- The host does **not** need the Vulkan SDK. It does need working GPU driver packages and Vulkan runtime support.

How the launcher chooses the GPU path:
- `scripts/docker-run-empirical-tests.sh` defaults to `--gpu-platform auto`.
- In `auto` mode, it prefers `nvidia` when `nvidia-smi` works on the host; otherwise it falls back to `drm` when `/dev/dri/renderD*` is available.
- You can override this explicitly with:
```bash
scripts/docker-run-empirical-tests.sh --gpu-platform drm
scripts/docker-run-empirical-tests.sh --gpu-platform nvidia
```

Recommended Ubuntu host setup:
```bash
# 1. Install Docker Engine.
sudo apt update
sudo apt install ca-certificates curl
sudo install -m 0755 -d /etc/apt/keyrings
sudo curl -fsSL https://download.docker.com/linux/ubuntu/gpg -o /etc/apt/keyrings/docker.asc
sudo chmod a+r /etc/apt/keyrings/docker.asc
sudo tee /etc/apt/sources.list.d/docker.sources <<EOF
Types: deb
URIs: https://download.docker.com/linux/ubuntu
Suites: $(. /etc/os-release && echo "${UBUNTU_CODENAME:-$VERSION_CODENAME}")
Components: stable
Signed-By: /etc/apt/keyrings/docker.asc
EOF
sudo apt update
sudo apt install docker-ce docker-ce-cli containerd.io docker-buildx-plugin docker-compose-plugin

# Optional: allow running docker without sudo.
sudo groupadd docker || true
sudo usermod -aG docker "$USER"
newgrp docker

# 2a. For Intel/AMD, install host Vulkan runtime packages.
sudo apt install mesa-vulkan-drivers vulkan-tools

# 2b. For NVIDIA, first install a working proprietary NVIDIA driver on the host.
# The simplest Ubuntu path is:
sudo ubuntu-drivers install
sudo apt install vulkan-tools

# 2c. For NVIDIA, install NVIDIA Container Toolkit and wire it into Docker.
curl -fsSL https://nvidia.github.io/libnvidia-container/gpgkey \
  | sudo gpg --dearmor -o /usr/share/keyrings/nvidia-container-toolkit-keyring.gpg
curl -s -L https://nvidia.github.io/libnvidia-container/stable/deb/nvidia-container-toolkit.list \
  | sed 's#deb https://#deb [signed-by=/usr/share/keyrings/nvidia-container-toolkit-keyring.gpg] https://#g' \
  | sudo tee /etc/apt/sources.list.d/nvidia-container-toolkit.list
sudo apt update
sudo apt install -y nvidia-container-toolkit
sudo nvidia-ctk runtime configure --runtime=docker
sudo systemctl restart docker
```

Host-side checks before running the empirical suites:
```bash
docker run hello-world
vulkaninfo --summary

# Intel/AMD path:
ls /dev/dri/renderD*

# NVIDIA path:
nvidia-smi
```

Interpretation of the checks:
- If `docker run hello-world` fails, Docker is not installed or not usable by your user.
- If `vulkaninfo --summary` fails or lists no physical devices, the host Vulkan stack is not ready.
- If `ls /dev/dri/renderD*` fails, the `drm` path is not available on that host.
- If `nvidia-smi` fails, the `nvidia` path is not available on that host.

Container-side note:
- The empirical image itself is built from [Dockerfile.empirical-tests](/home/zheyuan/gpu-subgroup_semantics-TLAPlus/Dockerfile.empirical-tests), which currently uses `ubuntu:22.04` and installs Amber plus Vulkan user-space packages inside the container. The host still must provide the real GPU device and working driver stack.

Run the evaluation subset:
```bash
scripts/docker-run-empirical-tests.sh
```
Expected runtime is about `5-8` minutes with a prebuilt image, or about `12-16` minutes if the Docker image is built from scratch as part of the run.

Run the full empirical suites:
```bash
scripts/docker-run-empirical-tests.sh --full
```

Outputs:
- Evaluation subset: `build/empirical_evaluation_results/`
- Full run: `build/empirical_full_results/`

Key files in either output directory:
- `summary.md`
- `summary.csv`
- `all_results.csv`
- `<suite>/*.log`

## GLSL
In our version of GLSL, we add additional syntax to take in TLA+ launch configuration
such as **Scheduler**, **subgroup size**, and **number of workgroup**.
You can check out the file under `example_shader_program` for more info.

### Scheduler
you can specify the scheduler for TLA+ model in shader program using following syntax:
```glsl
#pragma scheduler(<scheduler name>)
```
Currently we only support two scheduler: **HSA** and **OBE**
### Subgroup size
you can specify the subgroup size for TLA+ model in shader program similar to how you specify the workgroup size:
```glsl
layout(tla_subgroup_size = <num>) in;
```
num must be a **non-zero positive integer**
### Number of Workgroup
Similarily, you can specify the number of workgroup for TLA+ model in shader program using:
```glsl
layout(tla_num_workgroups = <num>) in;
```
num must be a **non-zero positive integer**.
### Synchronization Model
Select the SIMT-Step model with:
```glsl
layout(tla_synchronization_id = <id>) in;
```
`1` → SSO, `2` → SCF, `3` → SM, `4` → CM.

| `id` | Label | Collective instructions | Synchronous instructions | Independent instructions |
|------|-------|------------------------|--------------------------|--------------------------|
| 1    | SSO   | Subgroup ops (`OpGroup*`) | — | All remaining instructions |
| 2    | SCF   | Subgroup ops + control flow | — | Others |
| 3    | SM    | Subgroup ops + control flow | `OpAtomicLoad`, `OpAtomicStore`, `OpAtomicOr` | Others |
| 4    | CM    | Subgroup ops + control flow + all memory ops | — | Others |

**Limitation.** At present, the synchronous semantics for SM are only modeled for `OpAtomicLoad`, `OpAtomicStore`, and `OpAtomicOr`. Other atomic opcodes (e.g., `OpAtomicAdd`, `OpAtomicSub`, `OpAtomicExchange`) still execute independently; extending the synchronous rules to them is future work.

## Example:
`scripts/docker-run.sh --input example_shader_program/synchronization/cm.comp --out text`

## Command Line Option
- *format*: text, dot, all, fuzz


## List of supported SPIR-V Instructions
- OpVariable
- OpReturn
- OpLoad
- OpStore
- OpAtomicLoad
- OPAtomicStore
- OpBranch
- OpBranchConditional
- OpSwitch
- OpLabel
- OpLogicalOr
- OpLogicalAnd
- OpLogicalEqual
- OpLogicalNotEqual
- OpLogicalNot
- OpEqual
- OpNotEqual
- OpLess
- OpLessOrEqual
- OpGreater
- GreaterOrEqual
- OpAdd
- OpAtomicAdd
- OpSub
- OpAtomicSub
- OpMul
- OpSelectionMerge
- OpLoopMerge
- OpAtomicExchange
- OpAtomicCompareExchange
- OpGroupAll
- OpGroupAny
- OpGroupNonUniformAll
- OpGroupNonUniformAny
- OpControlBarrier

**Note**:
- The model treats the following instructions as equivalent:
    - `OpStore` and `OpAtomicStore`
- Global variables (e.g. Storage Buffer) are assigned to default values if they are not initialized in the function body.
    - For `uint` and `int` type, the default value is **0**.
    - For `bool` type, the default value is **true**.

## Supported Type
- int
- uint
- bool

## Memory Semantics
The model does not implement any extension to memory semantics, and all SPIR-V instructions
are behaving like `SequentiallyConsistent`.

## Reference
- https://lamport.azurewebsites.net/tla/safety-liveness.pdf


### Workflow Overview

```
scripts/docker-run.sh --input <shader.glsl> --out <format>
```
This runs `glslang` to generate SPIR-V, passes it to `Homunculus/src/main.rs` to produce TLA+ modules, and finally invokes TLC to model-check.

**Generated per-program artifacts**
- `forward-progress/validation/MCProgram.tla` – Overwritten by the pipeline with the program-specific instruction partitions, CFG, and dynamic-block metadata derived from the shader.

**Frontend pipeline**
- `example_shader_program/` – Annotated GLSL compute shaders used as evaluator-friendly fixtures; pragmas encode scheduler/subgroup/synchronization settings.
- `Homunculus/src/main.rs` & `compiler/src/codegen/*` – SPIR-V → TLA+ translation: parses `glslang` output, builds CFG/dynamic blocks, and emits the generated `MCProgram.tla` specialised to the shader while relying on the hand-authored `ProgramConf.tla` constant interface.
- `build/output.txt` – Sample TLC output from the Docker pipeline (helpful for confirming end-to-end execution).
