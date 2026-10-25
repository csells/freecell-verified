# Decision 0001: state model, search, evidence and interface

Status: adopted, 2026-10-25. Resolved from evidence during M0–M4; no user decision was required.

## Toolchain

Lean 4.35.0 via `lean-toolchain`, core and Std only. Mathlib was not needed: finiteness uses an explicit list (below) and `List.Nodup.length_le_of_subset` from core.

## Positions (`FreeCell/State.lean`)

`State` keeps the reference's shape — `cols : List (List Card)` with the exposed card first, `cells : List Card`, `home : List Nat` — and `Card` keeps natural-number rank and suit. Bounds live in `State.Valid` rather than in `Fin` types:

- exactly 8 columns and 4 foundation heights, each ≤ 13;
- at most 4 cells, strictly increasing by `Card.code` — interchangeable cells are a canonical sorted list, so equal cell multisets are equal states;
- `cols.flatten ++ cells ++ homeCards home` is a permutation of the 52-card deck, which forces genuine cards, no duplicates, no missing cards, and no overlap between physical cards and those implied by foundation heights.

Rationale: Nat arithmetic keeps rule proofs `omega`-friendly, and one permutation condition captures conservation, uniqueness and implicit foundation cards together. Validity is decidable (`State.decValid`) so input positions are checked at run time and the proof passed to the solver.

## Rules (`FreeCell/Rules.lean`)

Declarative `Pick`/`Put`/`Legal`/`Step` (inductive relations) are the trusted rules. Executable `pick`/`put`/`applyMove`/`succs`/`moves` are proved equal to them in both directions (`applyMove_eq_some_iff`, `mem_succs_iff`, `mem_moves_iff`). Moves are single-card. Foundation-to-tableau moves are excluded, cell-to-cell moves do not exist (cells are a set), and moving a lone card to an empty column is a legal (if pointless) move, exactly as in the #11982 reference — the differential test confirms identical successor sets on all 84,767 positions.

## Finiteness (`FreeCell/Finite.lean`)

`allShapes` is an explicit list containing every valid position: lists of at most 8 columns, each a list of at most 52 deck cards, at most 4 cells, 4 heights in 0–13. It is astronomically long and `noncomputable` so it is never compiled or evaluated (a first draft without `noncomputable` was evaluated at program start-up and exhausted memory; recorded in the M4 evidence). `length_le_stateBound` bounds any duplicate-free list of valid positions by its length.

## Reference search (`FreeCell/Search.lean`)

Depth-first search with a `HashSet State` visited set and a stack of frames, each frame carrying the reversed move list that reached it (so winning paths need no parent map). `step` pops one frame and expands it; the invariant `Inv` (reachability, no won visited position, replayable stack paths, closure-or-pending) is carried as a proof field of `Search`. A won successor ends the search with a path; an empty stack ends it with the visited set, which `checkClosed_of_inv` shows passes the generic closed-set checker. Each `Outcome` constructor carries the checker proof for its evidence, so every decided answer — from `solve` or from any bounded driver — is sound by construction.

Termination: `Search.measure = 2 * (stateBound - |visited|) + |stack|`. An expansion that adds k new positions pushes k frames and pops one, so the measure falls by k + 1; `|visited| ≤ stateBound` because visited positions are reachable from a valid start and hence valid. `run`/`solve` use well-founded recursion on this measure — no fuel and no `partial`. `runSteps_eq_run` shows `measure + 1` steps always suffice, which is the fuel bound derived from the algorithm.

Hash sets: `State` derives `DecidableEq` and `Hashable`; the `BEq` is lawful, so membership is equality and colliding hashes never merge distinct positions. All set reasoning uses Std's `HashSet` lemmas.

Search order: successors are pushed so that the first candidate (foundation moves, then columns) is explored first. Order does not affect any theorem.

## Evidence formats (`FreeCell/Codec.lean`, `FreeCell/Verify.lean`)

Certificates are line-oriented text with a format line, a rules identifier (`standard-freecell/single-card/4-cells/v1`), the start position and either a move list or a list of positions. Verification parses untrusted text, then checks the evidence against the start the caller requested, not the start the file names; a mismatched start line is rejected early for a clear message, and `verifyCertificate_winnable`/`verifyCertificate_unwinnable` hold for arbitrary text. Positions in certificates are not canonicalised or validated: the closed-set argument needs neither.

## Command line (`Main.lean`, `FreeCell/Driver.lean`)

`freecell solve | verify | deal | deals`. Limits: `--max-positions`, `--time-limit`, `--cancel-file`. External signals terminate the process without a result. Exit codes: 0 decided/accepted, 3 unknown, 4 certificate rejected, 2 usage or input error, 1 internal failure. When `--certificate` is given the file is written, read back and verified against the requested start before success is reported. Microsoft deals are accepted for 1–32000, the range checked against Freecell Solver's generator; validity of every deal number is proved, but layout parity beyond the checked range is not claimed.
