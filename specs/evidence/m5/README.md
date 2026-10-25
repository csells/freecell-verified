# M5 evidence: measurements and enabled optimizations

Host: Apple M5 Max, macOS 26.6.2, Lean 4.35.0. Other agents were building concurrently during some runs, so the timings are indicative only. Script: `tests/bench.sh FROM TO SECONDS [BINARY]`, one JSON line per deal, with each run using a pinned copy of the binary.

## Runs

| File | Engine | Deals | Limit | Decided | Unknown | Median time | p95 time | Median path |
|---|---|---|---|---|---|---|---|---|
| `bench-1-100-10s-reference-dfs-foundation-first.jsonl` | reference DFS only, foundation moves first | 1–100 | 10 s | 62 | 38 | 0.40 s | 5.0 s | 7,344 moves |
| `bench-1-1000-10s-proposer-then-reference.jsonl` | proposer (2M expansions), then reference DFS | 1–1000 | 10 s | 944 | 56 | 0.04 s | 1.2 s | 121 moves |

All 944 decided results are wins; every one was accepted by `checkWin` before being reported. Unknown is not a claim of unwinnability. Some of the 56 unknown deals are famous hard deals (e.g. 617, which needs about 18 s of proposer time on this machine). An earlier run of the reference-only configuration over deals 1–200 was stopped after 7 deals so the binary could be rebuilt, and its partial output was discarded; the 1–100 run above replaces it.

Spot checks: #11982 unwinnable, 84,767 positions, about 2 s. With `--reference-only`, the reference search with heuristic ordering found wins for #1 (18,503 moves), #2 and #3, but not #4, #617 or #1941 within 10 s.

## Enabled optimizations and their justification

1. **Successor ordering in the reference search** (`FreeCell/Heuristic.lean`, `orderedSuccs`). Successors are sorted by a heuristic score before being pushed. All search proofs quantify over membership, and `mem_orderedSuccs` (mergeSort is a permutation) gives the same membership. So `winnable_iff`, termination and evidence checking are unchanged. The differential count is unchanged too: 84,767 on #11982.
2. **Untrusted win proposer** (`FreeCell/Propose.lean`). This is a best-first search that also plays safe foundation moves. It is not a refinement of the reference search and has no termination or completeness proof. Its only effect is a candidate move list, which is reported only if `checkWin` (proved sound by `checkWin_sound`) accepts it. Results are labelled `engine: proposer` or `engine: reference`; `--reference-only` disables the proposer.

## Not enabled

Column-symmetry canonicalisation (83,239 positions on #11982) and safe-auto-move state reduction (61,643) were not implemented in the reference search. Each would need a proof that winnability is preserved and that witnesses can be reconstructed through the reduction. At present those counts are reproduced only by the prior independent Python evidence. Compact state encoding and faster frontier structures were not attempted either.

## Memory

Peak resident memory measured with `/usr/bin/time -l`: #11982 complete search 59 MB (84,767 positions); #617 via the proposer 299 MB (1.09 M positions); #4 reference-only, stopped at 10 s, 703 MB (1.75 M positions). That is about 400 bytes per visited position. The reference-only search on #4 without a time limit found a checked 618,847-move win after 63 s, peaking at 2.2 GB.

Incident, 2026-10-25 01:14: an early build of `freecell` evaluated the closed constant `allShapes` at startup and reached 178.9 GiB on a 128 GiB machine, forcing the user to close the session. The constant was made `noncomputable` the same night. The prevention added afterwards has two parts: `solve` now stops at 10,000,000 positions by default (`--max-positions unlimited` removes the cap), and every command in `scripts/check.sh`, `scripts/check-long.sh`, `tests/e2e.sh` and `tests/bench.sh` runs under `scripts/memguard.sh`. That script kills only its own command's process tree, by PID, once the tree's combined memory passes `FREECELL_MEM_MB` (default 16 GB).
