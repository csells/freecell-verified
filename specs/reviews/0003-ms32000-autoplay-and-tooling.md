# Review 0003: the 32,000-deal theorem, auto-play and tooling (adversarial)

Date: 2026-10-25. Subject: commit `69b7e11`. The scope is the headline claims in README.md, `specs/evidence/ms32000/README.md` and plan M7.

Three independent adversarial reviewers worked in parallel, each blind to the others. They covered proofs (statement fidelity, soundness, axioms), reproducibility (a fresh clone of the public repository, recomputed numbers, tamper controls, external sources) and tooling (memguard, the CLI cap, the proposer's path to verdicts, mutation testing, batch scripts). The coordinator reproduced the decisive findings (F1, F3, F5) before accepting them.

## Verdict

Every proof claim held:

- `ms32000_winnable_iff` states what the README says, over the real definitions. The case split covers 1–32000.
- Its axioms are exactly the three standard ones plus 33 `native_decide` axioms.
- `checkDealChunk_sound` and `checkWinCode_sound` are sound and use only standard axioms.
- The auto-play theorems are non-vacuous: real safe steps exist for both the ace/two case and the rank ≥ 3 case.
- A fresh clone builds the theorem in 33 s.
- Seven different data corruptions, plus a skip-list attack, all failed the build.
- Every published number was recomputed exactly from the archives.
- Keller's FreeCell FAQ and Wikipedia report #11982 as the only unsolvable deal of the 32,000.
- No path lets the proposer or a limit produce a wrong verdict.

The findings concern the tooling around the proof, the safety net and the provenance text. None changes a verdict.

## Findings

- **F1 (major for the safety story): memguard did not contain processes that reparent.** A detached grandchild allocated 150 MB under a 60 MB cap and finished; the guard exited 0. Separately, a bad cap (`-m abc`, `-m 0.5`, `FREECELL_MEM_MB=junk`) left the command running unguarded, and INT/TERM to the guard left grandchildren running.
- **F2 (minor): the forbidden-construct grep was bypassable.** It missed `@[inline] partial def`, `@[inline, extern …]`, `decide +native` and `@[ csimp]`. Nothing in the repository used these.
- **F3 (minor): provenance text was wrong.** The evidence README's regeneration command failed as printed (archive paths without their directory). The `fcsolve_moves.py` docstring claimed a `freecell verify` step that the code did not run; verification had been done by a separate script.
- **F4 (minor): tests weaker than their names.** Mutants that removed the default 10M cap, ignored `--max-positions unlimited`, or disabled the chunk line-count check all passed the tests.
- **F5 (minor): `tests/Axioms.lean` omitted `checkDealChunk_sound` and `checkWinCode_sound`.** Nothing compared the 32,000-deal theorem's axioms with the expected set; they were only printed.
- **F6 (minor): `solve_range.py` and `gen_bulk.py` edge cases.**
  - `solve_range.py` counted any exit-0 record as decided.
  - Its resume crashed on a torn last line.
  - `--only-from` skipped deals missing from the earlier file.
  - `gen_bulk.py` accepted empty move lists and wrote outside OUTDIR unchecked.
- **F7 (minor, wording):** the `autoWinnable_autoPlay_iff` docstring said "Microsoft-style", but Microsoft's exact rule is unverified.
- **F8 (disclosure):** `native_decide` also trusts compiled `String` code (`splitOn`), which the trust text did not mention.
- **F9 (cosmetic):** 31 "unused simp argument" warnings in the generated `Examples/Ms32000.lean`.

## Resolution (coordinator, 2026-10-25)

- **F1:** `scripts/memguard.sh` was rewritten.
  - The command runs as its own process-group leader (set with Perl's `setpgrp` before `exec`).
  - The guarded set is the group plus all descendants, so reparented processes are counted and killed.
  - INT/TERM/HUP are forwarded to the whole set, and processes left behind when the command exits are terminated.
  - The cap must be a positive integer, or the guard exits 2 without starting the command.
  - Kill paths signal only verified positive PIDs. While making this change the coordinator introduced a bug that sent `kill 0` when no members remained. The new tests caught it at once (the test shell itself was killed), it was fixed, and there is now a regression test: the caller must survive.
  - Remaining limit, documented in the script: a process that both calls `setsid` and loses its parent between two polls can escape.
  - `tests/memguard-test.sh` has 17 cases: pass-through, kill over cap, detached grandchild, leftover cleanup, six bad caps, TERM, INT, caller survival (×2) and overhead. It runs first in `scripts/check.sh`.
- **F2:** `tests/tools/forbidden.py` replaces the grep.
  - It strips comments and string literals, then matches 33 patterns anywhere in code, including `extern`, `implemented_by`, `csimp`, `partial`, `decide +native`, `ofReduceBool`, `attribute [`, `macro`, `elab`, `set_option`, `#eval` and `run_cmd`.
  - `scripts/check.sh` requires it to flag each of the 24 fixtures in `tests/fixtures/forbidden/flag/` and to pass `tests/fixtures/forbidden/pass/prose.lean`.
  - `Examples/` is scanned too, with only `native_decide` allowed.
- **F3:** the regeneration command uses full paths, and `scripts/check-long.sh` now runs it on every run and requires byte-identical output. `fcsolve_moves.py` now calls `freecell verify` and records a list as winnable only if it is accepted. A truncated list is rejected (checked).
- **F4:** `freecell solve --json` reports the effective `maxPositions`. There are e2e tests for the default (10,000,000), `unlimited` (null) and an explicit value. A new unit test, "chunk with an extra line rejected", is rejected only by the count check.
- **F5:** both theorems were added to `tests/Axioms.lean`.
  - `scripts/check.sh` requires one axiom report per `#print axioms` line, and only standard axioms.
  - `tests/tools/check_axioms.py` (run by `check-long.sh` over `tests/ExamplesAxioms.lean`) requires exactly the three standard axioms plus the 33 named `native_decide` axioms for `ms32000_winnable_iff`, and only the standard axioms for every kernel-checked deal.
  - `check-long.sh` also builds a tampered chunk and requires `native_decide` to reject it.
- **F6:**
  - `solve_range.py` counts a deal as decided only when exit is 0 and the result is winnable or unwinnable. It skips and terminates torn lines, and `--only-from` reruns every deal the earlier file did not decide.
  - `gen_bulk.py` requires exit 0, result winnable and a non-empty move list. It refuses an OUTDIR not named `Ms32000` and refuses a winning list for #11982. Malformed moves raise errors, not asserts.
- **F7:** the docstrings were reworded.
- **F8:** the README trust text now names the compiled checker and `String` code.
  - It also points to the new `Examples/Ms32000Kernel.lean`, which checks 15 stored wins with `decide +kernel` (kernel only, standard axioms only), cross-checking the compiled evaluation.
  - The 15 are #1, #2, #617, #1000, #1001, #1941, #11981, #11983, #31999, #32000, #853, #4213, #4232, #5174 and #5308. The last five were solved by Freecell Solver.
- **F9:** the generator emits `(by simp)` where no hypothesis is needed. The build has no warnings.

Verification of the fixes:

- `scripts/check.sh`: memguard tests 17/17; all 24 forbidden fixtures flagged; 22 axiom reports, all standard; Lean tests 94/94; e2e 63/63.
- `scripts/check-long.sh`: the 3 standard plus exactly 33 native axioms; 15 kernel-checked deals on standard axioms only; regeneration identical; the tampered chunk is rejected; 32,000 layouts identical.
- The build has no warnings.

Logs: `specs/evidence/m6/check-review0003.log` and `check-long-review0003.log`.
