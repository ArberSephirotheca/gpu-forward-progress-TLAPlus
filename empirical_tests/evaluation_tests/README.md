# Amber Evaluation Test Subset

This directory contains the evaluator-sized subset of the paper-aligned Amber suites used for the empirical investigation in the PLDI submission.

If you want the full empirical campaign instead, use the sibling directory `../full_tests/`.

Each suite contains:
- `reference.amber`
- `variant_000.amber` through `variant_008.amber`

That gives `10` Amber files per suite and `100` Amber files total across the evaluation subset. In practice, this subset is meant to finish in about `5-8` minutes with a prebuilt image.

Host requirements:
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

Suite naming:
- `cm`: Collective Memory
- `sm`: Synchronous Memory
- `scf`: Synchronous Control Flow
- `sso`: Synchronous Subgroup Operation
- `ww`: write-write race pattern
- `rw`: read-write race pattern
- `wr`: write-read race pattern

Suite mapping:
- `cm_wr`: Fig. 3 / CM. Tests whether memory operations are collective across the subgroup.
- `sm_ww`, `sm_rw`, `sm_wr`: Fig. 2 without the subgroup operation / SM. Tests whether memory operations stay synchronous inside a converged basic block.
- `scf_ww`, `scf_rw`, `scf_wr`: Fig. 9 without subgroup operations / SCF. Tests whether branch and merge points synchronize control-flow progress.
- `sso_ww`, `sso_rw`, `sso_wr`: Fig. 9 with subgroup operations / SSO. Tests whether subgroup operations synchronize with the surrounding control-flow dependencies.
