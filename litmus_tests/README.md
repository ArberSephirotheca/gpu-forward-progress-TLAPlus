These litmus shaders exercise `ww`, `wr`, and `rw` patterns for each direct semantics model:

- `cm_*`
- `sm_*`
- `scf_*`
- `sso_*`

Run them through the existing TLA+ pipeline with:

```bash
scripts/docker-run-tlaplus.sh --litmus-tests
```

Each `.comp` file is compiled into its own `MCProgram.tla`, and TLC output is written under `build/litmus_tests_result/`.

With the current RA memory extension enabled for scalar global/shared atomics, the `scf_wr`, `sm_wr`, and `sso_wr` shaders check per-thread self-visibility after the release RMW sequence. Peer-slot visibility is no longer guaranteed by the RA load semantics without an extra synchronization edge.
