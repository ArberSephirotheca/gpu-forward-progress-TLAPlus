# Empirical Tests

This directory contains the Amber suites used for the paper's empirical investigation.

- `evaluation_tests/`: evaluator-sized subset. Ten suites, with `101` Amber files per suite, intended to finish in a few minutes.
- `full_tests/`: full empirical campaign. Ten suites, with `10001` Amber files per suite, intended for evaluators who want the larger run.

The suite names correspond to the paper's direct SIMT-Step models and the memory access pattern:
- `cm`: Collective Memory
- `sm`: Synchronous Memory
- `scf`: Synchronous Control Flow
- `sso`: Synchronous Subgroup Operation
- `ww`, `rw`, `wr`: write-write, read-write, write-read
