# M0 evidence: reproduction and bootstrap

Run 2026-10-25 in this repository.

- Toolchain: elan 4.2.4 (Homebrew `elan-init`), `lean-toolchain` = `leanprover/lean4:v4.35.0`.
  `lean --version`: Lean (version 4.35.0, arm64-apple-darwin24.6.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release).
  `lake --version`: Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0).
- Host: macOS 26.6.2 (25G83), Apple M5 Max, 128 GiB.
- Reference file hash (unchanged): `4596577e7a3cc8dd73a78760ed45bb2a3572c01cfb4ce28a2f66651c65d3e93b`, matching `specs/references/freecell-11982/manifest.json`.
- Command: `lake env lean specs/references/freecell-11982/FreeCell11982.lean`
- Output: `reference-run.log` — byte-identical to `specs/references/freecell-11982/original-run.log` (`diff` empty): certificate size 84767; `freecell_11982_unwinnable` depends on `propext, Classical.choice, Quot.sound, certificate_ok._native.native_decide.ax_1_1`.
- Cost of this run (`/usr/bin/time -l`): 27.36 s real, 688,537,600 bytes maximum resident set (`reference-run.time`). This is a new measurement, not the historical runtime.
- `lake build` succeeds. Build output (`.lake/`) is ignored by git.

The copied `negative-controls.log` and `witness-replay.log` were read as prior evidence only. Fresh controls against the new code are in `FreeCellTest/Main.lean` and `tests/e2e.sh` (see the M2/M4 evidence).

Reproduce: `scripts/check-long.sh` (first section).
