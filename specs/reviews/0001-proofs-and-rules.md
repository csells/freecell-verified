# Review 0001: rules fidelity and proof soundness

Date: 2026-10-25. Independent adversarial review requested by the team lead. Scope: the claim that the project proves, for standard FreeCell, a sound, complete and terminating decision procedure over valid positions. The CLI, parsing and practical execution were reviewed separately and are out of scope here.

## Inputs

- `README.md`, `specs/vision/verified-freecell.md`, `specs/plans/0001-verified-freecell-solver.md`, `specs/decisions/0001-model-search-and-evidence.md`.
- `FreeCell/{Card,State,Rules,Valid,Finite,Reach,Cert,Search,Deal,Heuristic,Verify,Driver,Codec,Supermove}.lean`, `FreeCell.lean`, `lakefile.lean`, `scripts/check.sh`, `tests/Axioms.lean`.
- `lake build` (succeeded, Lean 4.35.0) and `lake env lean tests/Axioms.lean`.
- Scratch experiments in a `mktemp -d` directory under the session scratchpad (`T.lean`, `A.lean`): move enumeration on hand-built positions, `msDeal 1` validity, `winnable (msDeal 11982)` (returned `false`), axioms of the Supermove theorems and of `winnable`/`run`. No project file other than this report was changed.

## Verdict

No blocking or significant defect found. The headline statement

    winnable_iff : ∀ (start : State) (hv : start.Valid),
      winnable start hv = true ↔ ∃ t, Reachable start t ∧ t.Won

says what the README claims, rests only on `propext`, `Classical.choice` and `Quot.sound`, and `winnable` is a total function defined by well-founded recursion with a correct measure argument. The rules match standard (Microsoft) FreeCell for single-card moves. The findings below are disclosure gaps and check-script hardening, not unsoundness.

## Findings

### F1 — minor (scope disclosure): Microsoft's forced auto-play is not modelled, and the bridge is unproved

- Where: `FreeCell/Rules.lean:44-71` (`Pick`, `Put`, `Legal`), `README.md` "What is trusted"; not discussed anywhere in `specs/` except as a future optimisation at `specs/plans/0001-verified-freecell-solver.md:55`.
- Argument: Microsoft FreeCell automatically moves "safe" cards to the foundations; the player cannot decline. The model makes every foundation move optional. Every Microsoft play is therefore a model path (auto-moves are legal `Put.home` moves), so a model **unwinnable** verdict transfers to Microsoft's program. A model **winnable** verdict transfers only via the folklore argument that safe auto-moves never destroy a win (a simulation: moving a card home whose rank−1 opposite-colour cards are already home removes no useful option). That argument is sound as far as I can tell, but it is not proved, and a winning certificate is not guaranteed to replay verbatim in the Microsoft program, because auto-play can remove a card that a later certificate move names.
- Fix: state in README's "What is trusted" (or Scope) that the rules make foundation moves optional, that Microsoft's auto-play is outside the model, and which direction transfers without further argument. Optionally prove the safe-auto-move simulation lemma (the plan already lists it as an optimisation needing such a proof).

### F2 — minor: the Supermove theorems are listed as proved but not checked by `tests/Axioms.lean` or `scripts/check.sh`

- Where: `README.md` table row `Supermove.*`; `tests/Axioms.lean:18-30` prints axioms only for the other headline theorems.
- Demonstration: I printed them manually. `superReachable_iff : ∀ {s t : State}, s.Valid → (SuperReachable s t ↔ Reachable s t)` and `Supermove.reachable` both depend only on `[propext, Classical.choice, Quot.sound]`, so the claim currently holds. A later change that made these theorems depend on a new axiom would be caught by `check.sh` only if the grep happened to match the declaration (see F3), because the axiom gate never looks at them.
- Fix: add `#check @superReachable_iff`, `#print axioms superReachable_iff` and `#print axioms Supermove.reachable` to `tests/Axioms.lean`.

### F3 — minor: the forbidden-construct grep in `scripts/check.sh` is narrower than the README's assurance

- Where: `scripts/check.sh:6-9`.
- Argument: the regex `\bsorry\b|\badmit\b|native_decide|implemented_by|@\[extern|^\s*axiom\b|\b(partial|unsafe) def\b` misses `private axiom` / `noncomputable axiom` (the `axiom` alternative is anchored at line start), `unsafe` on anything but `def` (`unsafe instance`, `unsafe abbrev`), `opaque` declarations, `@[csimp]` (which replaces compiled code by a proved-equal one, harmless only if the lemma is real), and `set_option debug.skipKernelTC`. None of these occur in the library today (I grepped `FreeCell/`, `FreeCell.lean`, `Main.lean` for `implemented_by|extern|partial|unsafe|sorry|axiom|native_decide|admit|csimp|noncomputable|opaque|set_option|macro|elab|@[`; the only hits are two legitimate `noncomputable def`s in `Finite.lean`/`Search.lean`, kernel `decide` calls, and comments). The `#print axioms` gate covers the logical side for the listed theorems; the grep is what guards the compiled side, so it should be robust.
- Fix: broaden the pattern to `\baxiom\b`, `\bunsafe\b`, `\bopaque\b`, `@\[csimp`, `skipKernelTC`, or invert it (allowlist the expected `noncomputable def allShapes|stateBound|Search.measure`).

### F4 — note: `winnable_iff` derives its correctness from the `Outcome` type; termination carries the weight

- Where: `FreeCell/Search.lean:56-68, 265-285`.
- Observation: `winnable_iff` is proved as `(solve start hv).isWin_iff`, and `isWin_iff` holds for *any* value of type `Outcome start`, because each constructor carries a `checkWin`/`checkClosed` proof. So the theorem would hold for any total function into `Outcome start`; what makes it a decision procedure is that `run` is total. I checked that totality is genuine: `run` uses `termination_by σ.measure` with no `decreasing_by`; the decrease is the `Subtype` proof returned by `step` (`Search.lean:241-245`), derived by `omega` from `V'.size + rest.length = V.size + S'.length`, `V.size ≤ V'.size` and `V'.size ≤ stateBound` (`size_le_stateBound`, which uses `Reachable.valid` and `length_le_stateBound`). With k new positions the measure goes from `2(B−V) + |rest| + 1` to `2(B−V) + |rest| − k`. `stateBound` is `noncomputable` and astronomically large; it appears only in the measure, a `Prop` field, so it is erased from compiled code. This design is legitimate and is the stronger one (no search-correctness lemma can be wrong); it is noted only so readers do not look for a separate "the search is exhaustive" theorem. "Terminating" is a mathematical guarantee with an unusable bound, which the README already says under Costs.

### F5 — note: rule-variant choices

- Where: `FreeCell/Rules.lean:44-61`.
- No foundation-to-tableau moves; no cell-to-cell moves (a no-op under the set representation); no move of a card back onto its own column (`src ≠ .col j`, a no-op as well). These match classic Microsoft FreeCell. Under a variant that allows taking cards back from foundations, a model "unwinnable" verdict would not transfer (adding moves can only add wins); a "winnable" verdict would. README's Scope already says "no foundation-to-tableau" via the vision; worth one explicit sentence in README.

### F6 — note: `State.Valid` is a deliberate over-approximation

- Where: `FreeCell/State.lean:36-42`.
- `Valid` admits any arrangement of the deck into 8 columns, ≤ 4 canonical cells and consistent foundation heights, including tableau layouts no deal can produce. Every real position satisfies it (8 columns, ≤ 4 cells, foundations by height, one deck), so it excludes nothing real; including unreachable layouts only widens the theorems. It is not vacuous (`msDeal_valid`). The sorted-cells clause means a hand-built `State` with unsorted cells is rejected rather than mis-solved; the position parser sorts cells (`Codec.lean:64,102`). Certificate positions are not canonicalised (`Codec.lean:135`), which can only make an honest closed set fail to check, never make a non-closed set pass.

### F7 — note: README wording for `msDeal_valid`

- Where: `README.md` table, "every Microsoft game number deals a valid position".
- The theorem is `∀ game : Nat, (msDeal game).Valid`: it is about the project's `msDeal`, not Microsoft's program. Equality with Microsoft's layout is evidence for 1–32000 only, as the "What is trusted" section correctly says. Suggest "`msDeal n` is a valid position for every `n`".

## Checked and found sound

- **Card colours and stacking.** `Card.red` is diamonds/hearts (suits 1, 2); `Put.stack` requires one rank higher and different colour on the exposed card of another column.
- **Moves present.** Column → foundation, column → stack, column → empty column, column → free cell (only if fewer than 4 occupied), cell → foundation, cell → stack, cell → empty column. Foundation requires `home[suit] + 1 = rank`. Hand-built scratch positions produced exactly the expected successor lists (e.g. full cells suppress every `→ f` move; an ace and a 2H with AH home go home; 4C goes onto both 5H and 5D; no move targets a covered card).
- **Moves absent.** Foundation → anywhere, cell → cell, moves into an 9th+ column (`i < 8`, `j < 8` in `Pick`/`Put`).
- **Free-cell representation.** Cells are a strictly code-sorted list; `Src.cell c` requires `c ∈ cells`; `insertSorted`/`erase` keep the invariant (`Legal.valid`). Since cells are interchangeable in the game, the multiset representation loses no information relevant to winnability.
- **`Won`.** `home = [13,13,13,13]`; with `Valid`, `cards_perm` forces columns and cells empty, so it is exactly "all 52 cards home". `won`/`Won` agree (`won_iff`).
- **Executable = declarative.** `pick_eq_some_iff`, `put_eq_some_iff`, `applyMove_eq_some_iff`, `mem_succs_iff`, `mem_moves_iff` prove both directions; `candidateMoves` is shown to contain every legal move. `orderedSuccs` is a `mergeSort` with `mem_mergeSort`, so order never affects membership.
- **Validity preservation and finiteness.** `Legal.valid` via card-list permutation; `allShapes` genuinely contains every valid state (`State.Valid.mem_allShapes`) and `length_le_stateBound` uses `Nodup.length_le_of_subset`.
- **Checkers.** `checkWin_sound` and `checkClosed_sound` assume nothing about the evidence or the start's validity; `checkClosed` requires `start ∈ c`, no won member, and closure under `moves`, which is complete by `mem_moves_iff`.
- **Hash sets.** `State`/`Card` derive `DecidableEq` and `Hashable`; no custom `BEq` instance exists anywhere in the project (`grep instance`), so the `BEq` is the lawful one from `DecidableEq`, and all reasoning uses Std `HashSet` lemmas (`mem_insert`, `size_insert`, `distinct_toList`, `mem_iff_contains`). Hash quality affects only bucket choice. The toolchain's `Std/Data/{DHashMap,HashMap,HashSet}` sources contain no `implemented_by` or `@[extern]`, so compiled hash-set behaviour is the same Lean code the lemmas describe (modulo general compiler trust, already disclosed).
- **Search invariant.** `Inv`/`ExpInv` (reachability, no won visited state, replayable stack paths, closure-or-pending) are maintained by `expand_ok`; an empty stack yields `checkClosed_of_inv`; a won successor yields `expand_error` → `checkWin`. A won start is handled in `initSearch`.
- **Bounded driver.** `runChunk`/`searchLoop`/`solveBounded` (`Driver.lean`) can only return `decided` with an `Outcome` (proof-carrying) or `unknown`; the proposer's path is accepted only after `checkWin start ms = true` is established by `if h :`. `searchLoop` terminates by the same measure.
- **Certificates.** `verifyCertificate_{winnable,unwinnable}` hold for arbitrary text and bind to the caller's `start` (`c.start = start` by `DecidableEq`).
- **`msDeal`.** MSVC LCG `seed·214013 + 2531011 mod 2³¹`, output `seed / 2¹⁶` (equivalent to `(seed >> 16) & 0x7fff`), swap-with-last removal, dealing round-robin left to right with the last card exposed: matches the published Microsoft algorithm. `msDeal_valid` is proved for every `Nat`.
- **Supermoves.** Capacity `(free cells + 1)·2^(empty columns other than source and destination)` is the standard limit; `Lands` is vacuous for an empty destination as it should be. `superReachable_iff` gives both inclusions from a valid position.
- **Axioms.** All theorems in `tests/Axioms.lean`, plus `superReachable_iff`, `Supermove.reachable`, `winnable` and `run`, depend only on `propext`, `Classical.choice`, `Quot.sound` (`mem_succs_iff`, `mem_moves_iff`, `checkWin_sound` not even on `Classical.choice`). The library contains no `sorry`, `axiom`, `native_decide`, `partial`, `unsafe`, `implemented_by`, `extern` or `opaque`; `Examples` (which uses `native_decide`) is a separate `lean_lib` not imported by `FreeCell` or `Main`.

## Resolution (coordinator, 2026-10-25)

- F1: disclosed in README "Scope" (auto-play not modelled; unwinnable transfers, winnable relies on the unproved safe-auto-move argument; certificates may not replay verbatim in Microsoft's program). Not proved.
- F2: `Supermove.reachable` and `superReachable_iff` added to `tests/Axioms.lean`, which `scripts/check.sh` audits.
- F3: forbidden-construct pattern in `scripts/check.sh` broadened (any `axiom`, `opaque`, `unsafe`, `@[csimp]`, kernel-skipping options).
- F5, F7: README wording corrected. F4, F6: notes, no change.
