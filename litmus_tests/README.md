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
