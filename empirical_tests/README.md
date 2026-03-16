# Empirical Tests

This directory contains the Amber suites used for the paper's empirical investigation.

- `evaluation_tests/`: evaluator-sized subset. Ten suites, with `10` Amber files per suite (`reference.amber` plus `variant_000.amber` through `variant_008.amber`), intended to finish in about `5-8` minutes with a prebuilt image.
- `full_tests/`: full empirical campaign. Ten suites, with `10001` Amber files per suite, intended for evaluators who want the larger run.

The suite names correspond to the paper's direct SIMT-Step models and the memory access pattern:
- `cm`: Collective Memory
- `sm`: Synchronous Memory
- `scf`: Synchronous Control Flow
- `sso`: Synchronous Subgroup Operation
- `ww`, `rw`, `wr`: write-write, read-write, write-read
