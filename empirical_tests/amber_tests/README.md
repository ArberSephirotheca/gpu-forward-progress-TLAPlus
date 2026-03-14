# Amber Empirical Test Suites

This directory contains the paper-aligned Amber suites used for the empirical investigation in the PLDI submission.

Each suite contains:
- `reference.amber`
- `variant_000.amber` through `variant_099.amber`

Suite naming:
- `cm`: Collective Memory
- `sm`: Synchronous Memory
- `scf`: Synchronous Control Flow
- `sso`: Synchronous Subgroup Operation
- `ww`: write-write race pattern
- `rw`: read-write race pattern
- `wr`: write-read race pattern
