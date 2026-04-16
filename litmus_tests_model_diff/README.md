This directory previously held separate model-distinguishing `wr` shaders.

Those peer-visibility tests have now been promoted into `../litmus_tests/` so the default litmus suite stays close to the Amber references:

- `scf_wr`
- `sm_wr`
- `sso_wr`

Use `scripts/docker-run-tlaplus.sh --litmus-tests` and select `--memory-model plain` or `--memory-model ra` to exercise those cases.
