# Evidence: every Microsoft deal 1–32000

Result: `FreeCell.Examples.Ms32000.ms32000_winnable_iff` (`Examples/Ms32000.lean`):

    theorem ms32000_winnable_iff (n : Nat) (h1 : 1 ≤ n) (h2 : n ≤ 32000) :
        (∃ t, Reachable (msDeal n) t ∧ t.Won) ↔ n ≠ 11982

Axioms: `propext`, `Classical.choice` and `Quot.sound`, plus 33 `native_decide` axioms: one for each of the 32 chunk theorems and one for `deal11982_unwinnable`. The theorem therefore trusts Lean's compiler to evaluate `checkDealChunk` and `winnable` correctly. The checkers it evaluates are proved sound in the library without `native_decide` (`checkDealChunk_sound`, `checkWin_sound`, `winnable_iff`).

Host: Apple M5 Max, 18 cores, 128 GB, macOS 26.6.2, Lean 4.35.0, on 2026-10-25.

## How the winning move lists were found

How a move list was found plays no part in the proof. Lean re-checks every list with `checkWin` when `Examples/Ms32000/Chunk*.lean` is built.

| Pass | Source | Deals tried | Settings | Wins | Unknown | Other |
|---|---|---|---|---|---|---|
| 1 | proposer, `freecell solve` | 1–32000 | 20 s, 12 workers | 31,819 | 180 | #11982 unwinnable (complete search) |
| 2 | proposer | the 180 unknown | 300 s, proposer budget 10^8, `--max-positions 15000000`, 6 workers; reniced to 19 partway through | 107 | 73 | |
| 3 | Freecell Solver 6.16.0 (`fc-solve -p -t -sam`, default preset), expanded by `tests/tools/fcsolve_moves.py` | the 73 unknown | single process | 73 | 0 | |

Median solve times: pass 1 0.064 s (slowest win 20.9 s); pass 2 112 s (slowest 296 s). Median path length: 154, 220 and 201 single-card moves respectively. In total 31,999 move lists hold 5,287,846 moves, and Lean checks them all in under 30 s of build time. Pass 2 ran at nice 19 with background QoS after its first 36 deals, at the user's request. That lowered its effective time limit, so more of its deals ended unknown.

Proposer binary: built from commit `6c6cca8` plus the uncommitted proposer changes of this milestone (run moves expanded into single-card moves, column-order canonical dedup). Its sha256 is `be6798d028852956cebe489ccfb380f84c107fe6c306bb96af9d755bc229b081`.

Freecell Solver was built locally from release tarballs under `scratch/fc-solve/`:

| Artifact | sha256 |
|---|---|
| `freecell-solver-6.16.0.tar.xz` | `71b8882e68f1be62529069018d0c732b75078669077c96348279575849f34313` |
| `rinutils-0.10.3.tar.xz` | `f9e527d37a6cc8c7b8870ada63caa24f32ab0d29fd1116df3ebb686583030955` |
| `fc-solve` binary | `34d582887621554ab798c970ece0802ae59d3014b16cdf61771626f8f43526c6` |

Dependencies: CMake 4.4.4 and cpanminus from Homebrew; Template-Toolkit, `six` and `pysol_cards` installed locally under `scratch/`. All 73 of its converted move lists were accepted by `freecell verify` before generation, and again by the Lean build. It did not solve #11982 ("This scan generated 35265 states").

## Files

- `pass1.jsonl.gz`, `pass2.jsonl.gz`, `pass3-fcsolve.jsonl.gz`: every result line, with full move lists, as written by `tests/tools/solve_range.py` and `tests/tools/fcsolve_moves.py`. `pass*.progress` are their progress logs.
- Regenerate the Lean data with `python3 tests/tools/gen_bulk.py Examples/Ms32000 <(gzip -dc pass1.jsonl.gz) <(gzip -dc pass2.jsonl.gz) <(gzip -dc pass3-fcsolve.jsonl.gz)`. Later files override earlier ones.

## Controls

- Tampering: dropping the last move of deal 6001's line in a copy of Chunk07 makes `native_decide` evaluate `checkDealChunk 6001 1000 [] data07 = true` to false, and the build fails. The unmodified chunk checks from scratch in 0.9 s.
- `FreeCellTest` section "compact move lists": round trip of the encoding; truncated wins, wins for another deal, a wrong line count and an unskipped bad line are all rejected.
