# Plan 0001: verified standard FreeCell solver

Status (2026-10-25): M0–M4 COMPLETE; M5 PARTIAL; M6 PARTIAL; M7 COMPLETE. Each milestone ends with a status note naming its evidence. Read the vision for the scope and result contracts.

## Dependency order

Valid finite game model → generic evidence checkers → verified reference search → bounded executable interface → measured optimization → independent review.

A winning-path checker and a closed-set checker may be developed in parallel once the state and move semantics are stable. Optimization depends on the reference proofs and must not quietly replace them.

## M0 — Reproduce and bootstrap

Create a pinned Lake project, initially Lean 4.35.0. Preserve `specs/references/freecell-11982/FreeCell11982.lean` as evidence, not a mutable production module. Run it with the pinned toolchain, record actual output and axiom dependencies, and read the retained negative-control logs. Establish a small executable test command and CI-ready commands, without publishing a remote repository.

Acceptance: `lake build` succeeds; `lake env lean specs/references/freecell-11982/FreeCell11982.lean` succeeds and reports 84,767; report the exact version and environment. Do not infer a historical runtime from this new run. Commit no generated build output.

**Status: COMPLETE.** M0 evidence is in `specs/evidence/m0/README.md`. The original proof reproduced byte-identically: 84,767 positions, the same axioms, 27.4 s, using Lean 4.35.0 via elan. `lake build` succeeds. The fast checks are `scripts/check.sh` and the long checks are `scripts/check-long.sh`.

## M1 — Define valid finite positions and independent move semantics

Use bounded card/suit/rank representations or prove equivalent bounds. Define `ValidState` to enforce exactly eight columns, cell capacity, foundation bounds, and conservation/uniqueness of the full deck, including the implicit foundation cards. Make the representation of interchangeable cells explicit.

Define a declarative legal-move relation separately from executable successor enumeration. Prove enumeration soundness and completeness relative to that relation, and prove that moves preserve validity. Establish a finite universe for valid positions or a rigorous finite upper bound; a finite deck does not by itself prove an unrestricted `List Nat` implementation finite.

Generalize reachability to `Reachable start state`. Prove the Microsoft generator yields valid initial deals over the documented seed range. Check seed/layout parity against the independent upstream generator, including #1 and #11982. Model-check miniature games if helpful, but distinguish reduced-model tests from the 52-card theorem.

Acceptance: Lean-checked validity-preservation and move-enumeration theorems; explicit finiteness construction/bound; tests reject duplicate/missing cards, invalid foundation/card overlaps and incorrect dimensions. Resolve single-card versus supermove semantics with a constructive argument or appropriately scoped theorem.

**Status: COMPLETE.**
- Validity: `State.Valid` (`FreeCell/State.lean`). Moves preserve it (`Legal.valid`, `Step.valid`), and it is decidable (`State.decValid`).
- Declarative and executable rules agree: `Pick`/`Put`/`Legal` (`FreeCell/Rules.lean`) match `applyMove_eq_some_iff`, `mem_succs_iff` and `mem_moves_iff`.
- Finiteness: `allShapes` with `length_le_stateBound` (`FreeCell/Finite.lean`).
- Reachability is `Reachable start`, and `msDeal_valid` covers every game number. Deal layouts are identical to fc-solve 5c057b7's generator for deals 1–32000 (`scripts/check-long.sh`, `specs/evidence/m6/check-long.log`).
- Supermoves: `Supermove.reachable` and `superReachable_iff` (`FreeCell/Supermove.lean`) show that capacity-limited sequence moves give exactly single-card reachability.
- Rejection tests (duplicates, missing cards, foundation overlap, dimensions, cell canonicity): `FreeCellTest/Main.lean`, section "validity".
- Differential evidence: successor sets are identical to the #11982 reference on all 84,767 positions and on 20,000 positions each of 4 other deals. Edge count 314,366 equals the independent Python baseline.
- Miniature games were not model-checked.

## M2 — Generalize checked evidence for both outcomes

Generalize `checkCert` and `cert_sound` to arbitrary valid starting states. Add a winning-path checker and its soundness theorem. Certificates must identify the exact start, rule version and board encoding; a valid certificate for another deal cannot establish an answer for the requested deal.

Treat deserialization as untrusted. Decode into bounded validated values, reject malformed data, and ensure the checked result refers to the decoded input actually requested by the caller. Start with a simple deterministic format; compression and streaming can wait.

Acceptance: generic checker soundness theorems; #11982 still checks; independent winning witnesses for #1/#617/#1941 check. Reject empty negative certificates, missing initial states, missing reachable successors, inserted won states, corrupted paths and mismatched starting boards. A successful M2 is NOT completion of this project.

**Status: COMPLETE.**
- Checkers: `checkWin_sound` and `checkClosed_sound` / `not_winnable_of_checkClosed` (`FreeCell/Cert.lean`), for arbitrary starts.
- Certificate format: `FreeCell/Verify.lean`. Certificates name the rules identifier and the start, and `verifyCertificate_winnable` / `verifyCertificate_unwinnable` hold for arbitrary input text, checked against the caller's start.
- #11982 checks. Independent witnesses for #1 (115 moves), #617 (144) and #1941 (106), converted from the prior Python search (`specs/references/independent-witnesses/`, `tests/fixtures/`), verify.
- Negative controls (fresh, against the new code) live in `FreeCellTest/Main.lean` and `tests/e2e.sh`.

## M3 — Verify the reference search itself

Implement an intentionally simple frontier/visited search over valid states with full equality. State and prove invariants: discovered states are reachable, pending work covers unexplored successors, visited processing is accounted for, and finding a win yields a legal reconstructed path.

Prove termination with an explicit well-founded measure or a finite bound sufficient for the actual loop. Counting unseen states alone may not decrease when processing already-discovered pending states; account for pending work and duplicate handling. If using fuel, derive sufficient fuel from the algorithm and finite-state argument, rather than picking a large constant and calling it complete.

Prove the returned decision equivalent to existence of a reachable win. Frontier exhaustion must imply closure. Establish that extracted evidence passes the generic checkers. Audit any hash-set or map representation: hashes accelerate lookup; collisions must never merge unequal states.

Acceptance: general soundness, completeness and termination theorems in Lean, with printed axiom dependencies; no `partial` or unbounded oracle hiding the totality claim. Winning and losing CLI examples are only corollaries, not the evidence for universal correctness.

**Status: COMPLETE.**
- Search: `FreeCell/Search.lean`. The invariant `Inv` is a proof field of `Search`. Each `Outcome` carries its checker proof.
- `solve`/`winnable` use well-founded recursion on `Search.measure` (no fuel, no `partial`). `winnable_iff` gives soundness and completeness; `runSteps_eq_run` derives sufficient fuel.
- The hash set uses the lawful `BEq` from `DecidableEq`.
- Axioms: `tests/Axioms.lean` (propext, Classical.choice, Quot.sound only).
- Per-deal corollaries via `native_decide` are in `Examples/Deals.lean`. They add a native axiom, are kept outside the library, and take about 12 minutes to build.

## M4 — Expose a practical bounded CLI

Implement parsed numbered-deal and explicit-position input, configurable limits, outcome/evidence output and a standalone verification command. Publish command help and machine-readable output. Choose exact command names during implementation and document them before the end-to-end tests.

Connect the executable to the proved reference algorithm. If a separate optimized engine proposes evidence, label its relationship honestly: checked answer soundness is not proof of that engine’s termination or completeness. Keep the total reference decision procedure available. Time/memory limits govern the operational tool, not a fake mathematical promise that every board fits a machine.

Acceptance: end-to-end runs through the actual CLI for win, loss, invalid input, wrong-board certificate, zero/small budgets and cancellation. Limits yield unknown and no misleading impossibility claim. The documented checker rejects tampering. Runtime failures are surfaced as failures, not swallowed as unknown mathematical results.

**Status: COMPLETE.**
- CLI: `freecell solve|verify|deal|deals` (`Main.lean`, `FreeCell/Driver.lean`), with `--json` output and documented exit codes (README, `freecell help`).
- The bounded driver runs the reference search's own `step`, so its decided answers carry proofs.
- The untrusted proposer is labelled and only counts through `checkWin`.
- `tests/e2e.sh` has 57 end-to-end tests: win, loss, invalid inputs, wrong-board and relabelled certificates, tampering, zero and small budgets, time limit, cancellation file (before and during a run), and no certificate written on unknown.
- External signals kill the process without a result.

## M5 — Measure and prove optimizations

Benchmark before choosing an optimization. Candidate work includes interchangeable-column canonicalization, safe automatic foundation moves, compact state encoding and faster frontier structures. Each needs an appropriate proof of reachability/winning preservation or refinement to the reference algorithm, including witness reconstruction through symmetry. Avoid importing a heuristic because it happened to preserve #11982’s result.

Acceptance: each enabled optimization has a scoped proof, differential evidence and measured costs. Reproduce original #11982 counts only under the matching representation: 84,767 fixed-column/no-auto states; 83,239 under column symmetry; 61,643 with the tested safe auto-home policy. Different encodings can legitimately count differently.

**Status: PARTIAL.** Evidence: `specs/evidence/m5/README.md`.
- Two optimizations are enabled: proof-neutral successor ordering and the separately labelled checked proposer, both measured. Deals 1–1000 at 10 s: 944 checked wins and 56 unknown, against 62/100 decided for the earlier DFS-only configuration.
- The proposer now also makes multi-card run moves, written out as single-card moves, and treats positions that differ only in column order as duplicates. With these it solved 31,819 of deals 1–32000 at 20 s each (`specs/evidence/ms32000/`).
- Not done: column-symmetry and auto-move reductions of the reference search (83,239 / 61,643), compact encoding, and faster frontiers.

## M6 — Review and release preparation

Have independent adversarial reviewers attempt to break model fidelity, logical soundness, parsing/serialization, result binding, resource handling and provenance. Pin supported dependencies; add reproducible commands, CI configuration, examples and trust documentation. Keep long checks explicitly separate from fast checks, with neither silently skipped nor counted as passed.

Acceptance: all vision success criteria are met, review findings resolved or explicitly scoped, and fresh-checkout reproduction succeeds. Prepare a contribution proposal distinguishing completed standard-FreeCell guarantees from deferred variants. Ask for public repository/licensing/submission direction before those external actions; the current authorization only creates this local planning project.

## Risks and stop conditions

- Finite does not mean feasible. A theoretically complete reference search can be too costly on many deals; report that rather than weakening the proof claims.
- A generic checker can finish sooner than a verified search. Preserve it as a useful milestone without calling the broader task complete.
- Specification correctness is independent of Lean acceptance. Validate the rules against primary sources and a separately implemented oracle.
- Native evaluation expands the trusted base. Audit and document actual dependencies after changes; investigate alternatives only against explicit cost/benefit.
- Ask the user only when evidence leaves a genuine product tradeoff. A difficult lemma or a routine data-structure choice is not itself a reason to interrupt.

**M6 status: PARTIAL.**
- Two independent adversarial reviews were run: `specs/reviews/0001-proofs-and-rules.md` (no blocking or significant findings) and `specs/reviews/0002-cli-and-certificates.md` (no wrong verdicts; 7 minor findings). All their minor findings except the free-cell auto-play proof (disclosed instead) were resolved, with regression tests.
- Toolchain pinned. Fast and long check scripts are in place. Fresh-copy reproduction (working tree without `.lake`) is logged in `specs/evidence/m6/fresh-copy-check.log`.
- Remaining:
  - CI configuration was not added.
  - The repository is public at github.com/csells/freecell-verified under the MIT licence, at the user's direction. No release has been tagged.
  - The contribution proposal and any upstream submission await the user's direction.
  - Auto-play equivalence is now proved for safe policies (M7). That Microsoft's exact rule is such a policy is not verified.

## M7 — Settle the Microsoft 32,000 and forced auto-play

Added after M0–M6 at the user's direction. Goals: decide every Microsoft deal 1–32000 in one Lean theorem, and close the gap between standard FreeCell and a game that plays safe cards home automatically.

Acceptance: a theorem stating exactly which of deals 1–32000 are winnable, whose only non-standard axioms are explicit `native_decide` evaluations of proved-sound checkers, with tamper controls; and a general auto-play theorem with standard axioms only.

**Status: COMPLETE.**
- `ms32000_winnable_iff` (`Examples/Ms32000.lean`): for 1 ≤ n ≤ 32000, deal n is winnable iff n ≠ 11982. Its axioms are the standard three plus 33 `native_decide` evaluations: 32 chunks of `checkDealChunk`, whose soundness is `checkDealChunk_sound` in `FreeCell/Bulk.lean`, and the #11982 search. Evidence, provenance, hashes and controls are in `specs/evidence/ms32000/README.md`. Of the 31,999 winning move lists, 31,926 came from the proposer and 73 from Freecell Solver 6.16.0. All are untrusted inputs re-checked by `checkWin`.
- `FreeCell/AutoPlay.lean`, standard axioms only:
  - `SafeStep.winnable_iff`: a safe foundation move (an ace or a two, or a card whose opposite-colour foundations are at most one rank lower) preserves winnability. It also never lengthens the shortest win (`SafeStep.winsIn`).
  - `autoWinnable_iff`: for any auto-play policy that only makes safe moves, the forced-auto-play game has exactly the winnable starts of standard FreeCell.
  - `autoWinnable_autoPlay_iff` instantiates it with a concrete policy. That policy agrees with the proposer's `autoHome` on 300 deals and the positions one move into them (`FreeCellTest`, section "auto-play").
- Kernel cross-check: `Examples/Ms32000Kernel.lean` checks 15 of the stored wins with `decide +kernel` (standard axioms only), cross-checking the compiled evaluation.
- Adversarial review: `specs/reviews/0003-ms32000-autoplay-and-tooling.md`. Three independent reviewers found no wrong verdict and no flaw in the proofs. All nine findings, about tooling, tests and docs, are resolved there.
- Verification after the fixes (logs `specs/evidence/m6/check-review0003.log` and `check-long-review0003.log`):
  - `scripts/check.sh`: memguard tests 17/17; the forbidden-construct checker flags all 24 fixtures, with no hits in the sources; 22 axiom reports, all standard; Lean tests 94/94; e2e 63/63.
  - `scripts/check-long.sh`:
    - the original proof is identical;
    - `ms32000_winnable_iff` has exactly the 3 standard plus 33 `native_decide` axioms;
    - all 15 kernel-checked deals use only `propext` and `Quot.sound`;
    - the regenerated files are identical;
    - a tampered chunk is rejected by `native_decide`;
    - the 32,000 deal layouts are identical.
  - The axiom checker itself rejects a dropped chunk axiom, an extra axiom, `sorryAx` in a kernel deal and a missing report.
- Not verified: Microsoft's exact auto-play rule. If it only ever plays safe cards in this sense, `autoWinnable_iff` covers it; we found no primary documentation of the rule.
