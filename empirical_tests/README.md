# Empirical Tests

This directory contains the Amber suites used for the paper's empirical investigation.

- `evaluation_tests/`: evaluator-sized subset. Ten suites, with `10` Amber files per suite (`reference.amber` plus `variant_000.amber` through `variant_008.amber`), intended to finish in about `5-8` minutes with a prebuilt image.
- `full_tests/`: full empirical campaign. Ten suites, with `10001` Amber files per suite, intended for evaluators who want the larger run.

Host requirements for running these suites through Docker:
- `x86_64` Linux host
- Docker Engine
- either:
  - a Linux DRM GPU path, such as Intel or AMD, with `/dev/dri/renderD*`
  - or an NVIDIA GPU with NVIDIA Container Toolkit configured for Docker

Notes:
- The documented evaluator configuration remains Ubuntu `22.04` or `24.04`. The curated empirical results in this artifact come from Intel Iris Xe runs.
- The host does not need the Vulkan SDK.
- The launcher supports both `drm` and `nvidia` GPU modes on Linux.
- For exact install and verification commands, see the `Dockerized Empirical Runs` section in the top-level [README.md](/home/zheyuan/gpu-subgroup_semantics-TLAPlus/README.md).

The suite names correspond to the paper's direct SIMT-Step models and the memory access pattern:
- `cm`: Collective Memory
- `sm`: Synchronous Memory
- `scf`: Synchronous Control Flow
- `sso`: Synchronous Subgroup Operation
- `ww`, `rw`, `wr`: write-write, read-write, write-read
