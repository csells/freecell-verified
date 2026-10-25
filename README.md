# FreeCell Verified

A Lean 4 solver for standard FreeCell whose decision procedure is proved sound, complete and terminating on every valid position, with a command-line tool that returns checked evidence or an honest `unknown`.

The precursor is [Chris Sells’s FreeCell #11982 article](https://sellsbrothers.com/freecell-11982-proof), which proved one deal unwinnable. This project generalises that argument to every valid position. Status by milestone is in [the plan](specs/plans/0001-verified-freecell-solver.md); design choices are in [decision 0001](specs/decisions/0001-model-search-and-evidence.md).

## What is proved

All theorems below are checked by Lean with no `sorry` and depend only on Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound` (`lake env lean tests/Axioms.lean`).

| Theorem | Statement |
|---|---|
| `mem_moves_iff` | the executable move generator lists exactly the declarative single-card moves |
| `Legal.valid` | a legal move from a valid position gives a valid position |
| `length_le_stateBound` | valid positions are finitely many (explicit bound) |
| `msDeal_valid` | the project's `msDeal` (Microsoft's published dealing algorithm) yields a valid position for every game number; agreement with Microsoft's numbering is tested, not proved |
| `checkWin_sound`, `checkClosed_sound` | accepted winning paths and closed sets prove winnability and unwinnability |
| `winnable_iff` | the total search `winnable start hv` returns `true` exactly when a won position is reachable |
| `runSteps_eq_run` | `measure + 1` steps of the search always suffice and give the same answer |
| `verifyCertificate_winnable`, `…_unwinnable` | an accepted certificate file proves its verdict for the requested position, whatever the file contained |
| `Supermove.*` (see `FreeCell/Supermove.lean`) | capacity-limited sequence moves are compositions of single-card moves |
| `SafeStep.winnable_iff` | playing a safe card home (an ace or a two, or a card whose opposite-colour foundations are at most one rank lower) never changes whether a position is winnable |
| `autoWinnable_iff` | with forced auto-play by any policy that only plays safe cards, exactly the same starts are winnable as in standard FreeCell |
| `checkDealChunk_sound` | an accepted block of compact move lists proves each listed deal winnable |

### Every Microsoft deal 1–32000

    theorem ms32000_winnable_iff (n : Nat) (h1 : 1 ≤ n) (h2 : n ≤ 32000) :
        (∃ t, Reachable (msDeal n) t ∧ t.Won) ↔ n ≠ 11982

Of the original 32,000 Microsoft deals, #11982 is the only one that cannot be won (`Examples/Ms32000.lean`). Every other deal has a stored winning move list, 5.3 million single-card moves in all, which Lean replays through `checkWin` when the file is built. #11982 is settled by the complete search. This theorem uses `native_decide` for those evaluations: 33 axioms, one for each of the 32 blocks of 1,000 deals and one for #11982. It therefore trusts Lean's compiler as well as its kernel. How the move lists were found (our proposer for 31,926 deals, Freecell Solver for the hardest 73) does not matter to the proof; see `specs/evidence/ms32000/`.

`winnable` is defined by well-founded recursion — no fuel, no `partial` — so termination is part of the definition being accepted.

## What is trusted

- **The rules.** `FreeCell/Card.lean`, `State.lean` (`Valid`, `Won`), `Rules.lean` (`Pick`, `Put`, `Legal`) and `Reach.lean` (`Reachable`) say what FreeCell is. Lean cannot check that they match the game; they were compared against the #11982 reference and an independent Python implementation (identical successor sets and 314,366 edges on all 84,767 positions of deal #11982) and against independently found winning paths.
- **Microsoft numbering.** `msDeal` is checked against Freecell Solver's generator for deals 1–32000 (`scripts/check-long.sh`), not proved equal to Microsoft's program.
- **Execution.** The command line is compiled Lean code. Its decided answers carry Lean proofs about the values computed, but running it trusts the Lean compiler and runtime, as any executable does. `Examples/Deals.lean` states per-deal corollaries with `native_decide`, which records that trust as an axiom.
- **The win proposer** (`FreeCell/Propose.lean`) is an unproved best-first search used only to find winning paths fast. Its proposals count only after the proved `checkWin` accepts them, and unwinnability is only ever decided by the proved reference search. Move lists from Freecell Solver, used for 73 hard deals in the 32,000-deal theorem, are treated the same way.

## Build and check

Requires [elan](https://github.com/leanprover/elan); `lean-toolchain` pins Lean 4.35.0.

    lake build                 # library and the freecell executable
    scripts/check.sh           # forbidden constructs, axioms, Lean tests, CLI tests (~4 minutes)
    scripts/check-long.sh      # original #11982 proof, native_decide corollaries incl. all 32,000 deals, deal parity (~15 minutes; needs cc)

## Using the solver

    $ .lake/build/bin/freecell solve --deal 11982
    unwinnable: every reachable position explored (84767 positions)
    $ .lake/build/bin/freecell solve --deal 1 --certificate deal1.cert
    winnable: 165 moves (found by the proposer search, checked)
    $ .lake/build/bin/freecell verify --deal 1 deal1.cert
    certificate accepted: the position is winnable

`freecell help` lists every option. Positions come from `--deal N` (Microsoft deals 1–32000) or `--position FILE`:

    Foundations: C-0 D-A H-2 S-0
    Freecells: QS 5H - -
    : KD QC JD
    : 5S
    ... (exactly eight column lines, cards bottom to top; ':' alone is an empty column)

Limits `--max-positions`, `--time-limit` and `--cancel-file` end the search with `unknown`, which is never an impossibility claim. Each visited position costs about 400 bytes, so `solve` stops at 10,000,000 positions (roughly 4 GB) unless given `--max-positions N` or `--max-positions unlimited`; `--reference-only` skips the proposer. `--json` gives machine-readable output. Exit status: 0 decided or certificate accepted, 3 unknown, 4 certificate rejected, 2 usage or input error, 1 internal failure.

Certificates record the rules identifier, the starting position and either a move list (`c3 h`, `c3 c5`, `c3 f`, `f:QS c2`) or every position of a closed set. `verify` checks them against the position you name on the command line.

## Costs

Finite does not mean fast. Deal #11982's complete search visits 84,767 positions in about two seconds on an Apple M5 Max. The proved search is exhaustive and can run for a very long time or exhaust memory on deals with huge reachable sets; the proposer usually finds wins for ordinary deals in well under a second. Measured results are in `specs/evidence/m5/`. No performance guarantee is made.

## Scope

Standard FreeCell only: 52 cards, eight columns, four cells, single-card move semantics (supermoves within the usual capacity are shown equivalent). Cards never return from a foundation, and free cells are interchangeable, so there are no cell-to-cell moves. Microsoft's program also plays some cards home automatically. `autoWinnable_iff` proves that forced auto-play changes nothing about which positions are winnable, as long as the policy only plays safe cards. That Microsoft's exact rule is such a policy is not verified here. A winning certificate is a standard single-card move list, and may not replay move for move in a program that auto-plays. Other solitaire games, other cell counts, shortest solutions and a GUI are not covered.

## License

MIT; see [LICENSE](LICENSE). The two headers in `specs/references/fc-solve-5c057b7/` are copied unmodified from [Freecell Solver](https://fc-solve.shlomifish.org/) (Copyright (c) 2000 Shlomi Fish, MIT/Expat licence) and keep their own notices.
