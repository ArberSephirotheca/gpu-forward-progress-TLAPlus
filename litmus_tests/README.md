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

The current litmus shaders are written to stay close to the Amber references while still staying inside the currently supported global/shared atomic fragment of the executable model:

- `cm_wr` still checks collective/uniform visibility.
- `scf_rw`, `sm_rw`, and `sso_rw` now use indexed atomics over `slots[tid]` / `slots[next]`, mirroring the Amber `read own, then write peer` shape.
- `scf_wr`, `sm_wr`, and `sso_wr` now use indexed atomics over `slots[tid]` / `slots[next]`, mirroring the Amber `write peer, then read own` shape.
- `scf_ww`, `sm_ww`, and `sso_ww` now use a two-element storage-buffer array and indexed atomics, so each thread overwrites `slots[tid]` with `1` and `slots[next]` with `2` before loading `slots[tid]` back.
- `sm_ww` now matches the Amber source shape directly, with no branch around the second store.
- `sso_ww` keeps the Amber-style `subgroupAll(true)` / `subgroupAll(false)` split before the peer overwrite.

With the current scalar RA memory extension, several regression tests behave differently by memory model:

- Under `Plain`, all regression shaders are expected to pass.
- Under `RA`, `scf_wr`, `sm_wr`, and `sso_wr` are expected to fail, because an acquire load is allowed to read any write at or after the thread's current per-location view; it is not forced to observe the peer's latest write.
- Under `RA`, `scf_ww`, `sm_ww`, and `sso_ww` are expected to fail too, because the final load of the thread's own address may still read the earlier self-write `1` instead of the later peer overwrite `2`.

The runner compares actual TLC outcomes against those expectations automatically.
