# Review 0002: command line and certificates (adversarial)

Date: 2026-10-25. Reviewer: independent adversarial agent. Scope: `Main.lean`, `FreeCell/Codec.lean`, `FreeCell/Verify.lean`, `FreeCell/Cert.lean`, `FreeCell/Driver.lean`, `FreeCell/Propose.lean`, `Outcome`/`step`/`initSearch` in `FreeCell/Search.lean`, `tests/e2e.sh`, `FreeCellTest/Main.lean`, README and decision 0001.

Binary under test: `.lake/build/bin/freecell` built 01:56:59, newer than every source file (latest source edit `FreeCell/Driver.lean` 01:53:48). Not rebuilt. All experiments ran in a fresh `mktemp -d` scratch directory; no project file other than this report was changed. Every process started was waited on or killed by its own PID.

## Verdict

No wrong result found. I could not get the executable or `verify` to report `winnable`, `unwinnable` or `certificate accepted` for a position where that is false, or for a position other than the one named on the command line. Every decided message traces to an `Outcome start` (carrying the `checkWin`/`checkClosed` proof) or to `verifyCertificate start …`, with `start` the validated requested position. Limits never produced an impossibility claim, a certificate, or exit 0.

The findings below are about misleading resource accounting, file-handling hazards and diagnostics. None is blocking.

## Findings

### F1 (minor, borders on significant): `--max-positions` overshoots by about a thousand in the proposer phase and reports the proposer's count

- Where: `FreeCell/Driver.lean:101-103`. The limit is checked only before each proposer chunk of `chunkSize = 1024` expansions, and against `p.seen.size` (the proposer's own set), not against the reference search's visited set.
- Reproduce:
  `freecell solve --deal 11982 --max-positions 5` → `unknown: position limit reached after visiting 1189 positions`
  `freecell solve --deal 617 --max-positions 100` → `… after visiting 1357 positions`
  `freecell solve --deal 11982 --max-positions 0` → `… after visiting 1 positions` (the first check runs before any chunk)
- Observed: a budget of N allows up to 1024 proposer expansions, each with many successors, before the check. The reported number is the proposer's `seen` size, while the help text says "give up (unknown) after visiting more than N positions". The proposer and the reference search also have separate budgets, so a run that passes the proposer phase can visit up to about 2N positions in total.
- Expected: the usage and README wording suggest a cap that holds to within one expansion and covers all search work.
- Soundness impact: none. The result is still `unknown` with exit 3.
- Suggested fix: when `maxPositions` is set, cap the proposer chunk at `max 1 (maxPositions - p.seen.size)`, or check the limit inside `Proposer.run`. Alternatively, document that the limit applies to each phase separately, with a granularity of one chunk. Label the reported count with its phase, for example `"phase":"proposer"` in JSON.

### F2 (minor): `--certificate` silently overwrites any existing file, including the input position

- Where: `Main.lean:115` (`IO.FS.writeFile path …`).
- Reproduce: `cp d1.txt in.txt; freecell solve --position in.txt --certificate in.txt` → exit 0, and `in.txt` now holds the certificate. The user's position file is gone.
- Expected: the project's data-preservation rule suggests refusing at least when the certificate path is the position path, or when the file already exists.
- Suggested fix: refuse when `--certificate` resolves to the `--position` file. Consider a `--force` flag before replacing an existing file. Write to `path.tmp` and rename it into place after verification (this also fixes F3).

### F3 (minor): an interrupted or failed certificate write leaves an empty or partial file on disk

- Where: `Main.lean:115-120`. The file is written in place and is not removed if the run is interrupted or the re-check fails.
- Reproduce: start `freecell solve --deal 11982 --reference-only --certificate p.cert`, poll until `p.cert` exists, then `kill -TERM <pid>`. Exit 143, no stdout, and `p.cert` is 0 bytes. `freecell verify --deal 11982 p.cert` then gives `certificate rejected: truncated certificate header`, exit 4.
- Observed vs expected: no false acceptance is possible, because `verify` rejects it. But a previous good certificate at that path is destroyed. If the internal re-check fails, an unverified file is left behind as well.
- Suggested fix: write to a temporary file in the same directory, verify that file, then rename it atomically. Delete the temporary file on failure.

### F4 (minor): an unwritable certificate path surfaces as an uncaught exception with exit 1, and `--json` emits nothing on stdout

- Where: `Main.lean:115`. `IO.FS.writeFile` throws an `IO.Error` that `CliM`'s `InputError` handler does not catch, so it propagates out of `main`.
- Reproduce: `freecell solve --deal 1 --certificate /nonexistent-dir/x.cert` → stderr `uncaught exception: no such file or directory … file: /nonexistent-dir/x.cert`, exit 1. The same happens for a read-only directory (error 13) and for `--certificate .` (error 21). With `--json`, stdout is empty.
- Assessment: the failure is surfaced correctly. It is not success and not unknown, and no verdict is printed. However, exit 1 means "internal failure" in `freecell help`, while this is an environment or input error. Also, the solve's work is lost without telling the user whether the position was decided.
- Suggested fix: catch IO errors around the write and read-back and report them as `error: cannot write certificate …`. Choose exit 2 (input/environment), or keep 1 and document it. In `--json` mode, emit `{"error":…}` on stdout.

### F5 (minor): `deals FROM TO` has no range check, unlike `deal` and `--deal`

- Where: `Main.lean:163-172`.
- Reproduce: `freecell deals 0 0` prints a layout for game 0. `freecell deals 32001 32001` prints a layout outside the range checked for Microsoft parity. `freecell deals 5 1` prints nothing and exits 0. By contrast, `freecell deal 0` gives exit 2, `deal must be between 1 and 32000`.
- Expected: README and decision 0001 say Microsoft deals are accepted for 1–32000 and that parity beyond that range is not claimed. `deals` contradicts this silently.
- Suggested fix: apply the same `1 ≤ g ≤ maxDeal` check and require `FROM ≤ TO`.

### F6 (minor): numeric options accept `_` digit separators and leading zeros

- Where: `Main.lean:44-47`, which relies on `String.toNat?`.
- Reproduce: `freecell solve --deal 1_1982 --max-positions 5` runs deal 11982. `--deal 01` runs deal 1.
- Impact: a typo such as `1_1982` meant as deal 1 or 1982 is accepted as deal 11982 without warning. The verdict is still correct for the deal actually solved, but that deal is not visibly named in the output.
- Suggested fix: accept only `[0-9]+` (optionally without leading zeros). Echo the deal number or position in the output (text and JSON) so the subject of the verdict is explicit.

### F7 (minor): irrelevant options are silently ignored, and repeated options silently override

- Where: `Main.lean:49-66`. The commands do not check which options they accept.
- Reproduce: `freecell verify --deal 1 --max-positions 3 --moves --certificate zzz 1.cert` → accepted, exit 0. `--certificate` and the limits have no effect. `freecell deal 1 --json` prints text. `freecell solve --deal 1 --deal 2 …` uses deal 2.
- Impact: a user who passes `--certificate X` to `verify` may believe X was checked, when the positional argument was checked instead. No false verdict results.
- Suggested fix: reject options a subcommand does not use, and reject repeated `--deal`/`--position`.

### F8 (note): input that cannot be a certificate is reported as "certificate rejected" (exit 4)

- Reproduce: `cat d1.txt | freecell verify --position - -`. Standard input is consumed by the position, so the certificate is empty, and the output is `certificate rejected: truncated certificate header`, exit 4.
- Suggested fix: reject using `-` for both the position and the certificate, with exit 2.

### F9 (note): a UTF-8 byte-order mark breaks parsing, with an obscure message

- Reproduce: a BOM-prefixed position gives `error: position: invalid card '﻿Foundations:'` (exit 2). A BOM-prefixed certificate gives `certificate rejected: expected 'freecell-verified certificate v1', found '﻿freecell-verified …'` (exit 4). In the second message the BOM is invisible.
- Suggested fix: strip a leading U+FEFF before parsing.

### F10 (note): `certificateVerified: false` in JSON when no certificate was requested

- Where: `Main.lean:113, 127, 134`.
- Observed: `freecell solve --deal 1 --json` → `"certificate":null,"certificateVerified":false`. A consumer can read this as "verification failed".
- Suggested fix: emit `null`, or omit the field, when no certificate was requested.

### F11 (note): a rejected proposer path is silent

- Where: `FreeCell/Driver.lean:115-119`. If `checkWin` rejects a proposal, the driver falls through to the reference search without any trace.
- Soundness: correct; the proposer influences the result only through `checkWin`. But a proposer regression, such as an illegal `autoHome` move, would show up only as slowness.
- Suggested fix: print a warning on stderr, or add a JSON field (`"proposerRejected": true`), and add a test that counts this event across the deal sample.

### F12 (note): `--time-limit` does not cover certificate writing and re-verification, and the default proposer budget is large

- Writing and re-checking an unwinnable certificate is not time-limited; for 11982 the file is 14 MB. A huge closed set could take long after the limit has passed.
- With the default `--proposer-budget 2000000`, the proposer ran 18.4 s and reached about 300 MB maximum RSS on deal 617 before it succeeded. On a deal where it fails, the whole budget is spent before the proved search starts. No soundness impact; worth stating in the Costs section of the README.

## Checked and found sound

- **Binding of results to the requested start.** `cmdSolve` gets `start` from `requestedStart` (`Main.lean:104`), and `solveBounded` returns `Result start`, whose `decided` constructor holds an `Outcome start` that carries the checker proof. `cmdVerify` calls `verifyCertificate start text` with the requested `start` (`Main.lean:144`). The certificate's own `start:` line is used only for an early mismatch check (`Verify.lean:91`); evidence is always checked against the caller's `start`. A certificate's start line relabelled to another deal is rejected (e2e covers both directions).
- **Write-then-verify.** The certificate is re-read from disk and verified against the requested `start` before anything is printed (`Main.lean:114-120`). On an unknown result no file is written (re-tested with `--max-positions 10 --certificate`).
- **Free-cell canonicalisation.** `parsePosition` sorts the cells (`Codec.lean:102`). Cells are interchangeable in the rules (`State.lean` documentation, decision 0001), so the solved position is the same game position. Foundations are per suit; duplicates (`C-0 c-0`) are rejected. Overlap between foundation heights and physical cards is caught by `Valid.cards_perm`. A missing Foundations/Freecells line defaults to empty, and the deck-permutation check then rejects anything inconsistent.
- **Parser robustness.** CRLF line endings (both formats), lowercase cards, `10D` for `TD`, columns without a leading `:`, extra `-` entries in Freecells, 9 columns, 0 columns, empty stdin, a directory as input, non-UTF-8 input (exit 2, `cannot read … non UTF-8 data`), more than 4 cells, and a duplicate Foundations or Freecells line. All were rejected with exit 2, or accepted with the correct meaning.
- **Round-trip.** `FreeCellTest/Main.lean:198-202` tests `parse ∘ print` for both formats over a sample. `verify` of the 84,767-position 11982 certificate, accepted from disk, also exercises `parseCompact ∘ showCompact` on every reachable position of that deal. The only non-round-tripping input found was a state with zero columns (`showCompact` prints `h|c|`, which parses back as one empty column). The tool never emits such a state, and certificate positions do not need validity for soundness.
- **Certificate tampering.** Count mismatches, deleted moves, extra positions, a won position inserted into a closed set, an empty closed set, `winnable: 0` for a non-won start, a wrong rules id, truncation and garbage were all rejected with exit 4 (e2e, plus a manual `winnable: 0` case).
- **Limits.** `--max-positions 0`, small values and large values; `--time-limit 0`; `--cancel-file` existing at start, created mid-run, or equal to the certificate path. All gave `unknown`, exit 3, `this is not an impossibility proof`, and no certificate. Reference-phase accounting is tight: `--reference-only --max-positions 84766` on 11982 gives unknown, and `84767` gives `unwinnable`. A trivially won start decides even with `--max-positions 0`, which is correct because `initSearch` decides it before any search.
- **Signals.** SIGTERM and SIGINT during the search end the process with no stdout and a signal status (143 or −2), so no verdict is printed. The only side effect is F3.
- **The untrusted proposer.** It can reach the output only through `solveBounded` (`Driver.lean:115-117`), guarded by `if h : checkWin start ms = true`, whose proof builds `Outcome.win`. Unwinnability is produced only by `searchLoop` (the proved `step`) or `initSearch`. The proposer can at most cause `unknown` (by consuming the limits; see F1) or slowness.
- **Exit codes and JSON.** These match `freecell help` and README: 0 for decided or accepted, 3 for unknown, 4 for rejected, 2 for usage or input errors (unreadable files, invalid positions, bad options, deal out of range). The exceptions are F4 (exit 1 for a certificate-write failure) and F8. JSON output parses and its fields agree with the text output.

## Not checked

- Behaviour under real out-of-memory conditions; macOS does not enforce `ulimit -v`, so I did not try to provoke it.
- SIGPIPE or a closed stdout during output.
- Positions that are not 52-card-consistent but encoded only through certificate closed-set lines. `checkClosed_sound` makes them irrelevant to soundness, so they were not fuzzed.

## Resolution (coordinator, 2026-10-25)

Regression tests for each item are in `tests/e2e.sh` ("review 0002 regressions").

- F1: `--max-positions` now bounds proposer and reference together; the proposer checks the limit before every expansion (`Proposer.run`), so overshoot is at most one position's successors. `solve --deal 11982 --max-positions 5` now stops after at most ~15 positions.
- F2: `--certificate` refuses an existing path (exit 2).
- F3: certificates are written to a temporary file and renamed into place.
- F4: write failures are reported as `error: cannot write certificate …`, exit 1 ("runtime failure" in help), with a JSON error object under `--json`.
- F5: `deals` requires 1 ≤ FROM ≤ TO ≤ 32000.
- F6: numbers must be plain decimal digits (`1_1982` rejected). Leading zeros remain accepted (`01` = 1).
- F7: options are checked per command and may not repeat.
- F8: `verify --position - -` rejected. F10: `certificateVerified` is `null` when no certificate was requested. F11: a rejected proposer path prints a warning on stderr. F12: help documents that limits are checked between batches and the time limit excludes certificate writing. F9 (BOM message): unchanged.
