These litmus shaders are the regression litmus suite. They exercise `ww`, `wr`, and `rw` patterns for each direct semantics model:

- `cm_*`
- `sm_*`
- `scf_*`
- `sso_*`

Run the regression suite with:

```bash
scripts/docker-run-tlaplus.sh --litmus-tests
```

Each `.comp` file is compiled into its own `MCProgram.tla`, and TLC output is written under `build/litmus_tests_result/`.

The current litmus shaders are written to stay close to the Amber references while still using a single packed scalar location instead of indexed buffers:

- `cm_wr` still checks collective/uniform visibility.
- `scf_rw`, `sm_rw`, and `sso_rw` read the thread's own slot and then write the peer slot.
- `scf_wr`, `sm_wr`, and `sso_wr` write the peer slot and then read the thread's own slot.
- `scf_ww` and `sm_ww` write the thread's own slot first and then the peer slot.
- `sso_ww` also mirrors the Amber branch-specific `subgroupAll(true)` / `subgroupAll(false)` shape.

With the current scalar RA memory extension, those peer-visibility `wr` tests behave differently by memory model:

- Under `Plain`, all regression shaders are expected to pass.
- Under `RA`, `scf_wr`, `sm_wr`, and `sso_wr` are expected to fail, because an acquire load is allowed to read any write at or after the thread's current per-location view; it is not forced to observe the peer's latest write.

The runner compares actual TLC outcomes against those expectations automatically.
