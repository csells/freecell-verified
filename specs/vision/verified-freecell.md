# Vision: a verified solver for standard FreeCell

Status: implementation direction, 2026-10-25. The reference solver and its general theorems are implemented; see the plan for milestone status (M5 and M6 partial).

## Problem and desired outcome

The existing #11982 artifact proves one Microsoft deal unwinnable by checking a finite closed set. Freecell Solver’s [broader to-do](https://github.com/shlomif/fc-solve/blob/master/fc-solve/site/wml/src/to-do.html.tt2#L144) asks for a solver with a formally verified correctness proof, motivated by this and other impossible deals.

Build a reusable solver for standard FreeCell, not merely a script that runs the existing proof on another seed. Given any valid position, an unrestricted reference solver must terminate and decide whether a winning position is reachable. A practical bounded implementation returns a checked answer or an explicit unknown result. These are different contracts; both must be documented and connected by proofs where claimed.

The intended users are maintainers reviewing the mathematics, developers reproducing a result, and players asking whether a deal can be won. A simple command-line tool and inspectable Lean sources are sufficient. A GUI is not part of the first release.

## Initial scope

- Standard 52-card deck, eight tableau columns, four interchangeable free cells, four ascending suit foundations; descending alternating-color tableau stacking; no foundation-to-tableau moves.
- Arbitrary valid positions, including partially played positions. Validation accounts for cards implicitly represented by foundation heights as well as cards physically present in columns and cells.
- A Microsoft numbered-deal adapter with an explicitly documented and independently checked seed range. Start with the original 1–32,000 deals; never imply parity with every later or third-party numbering scheme.
- Single-card transitions as the foundational semantics. Establish the precise relationship to capacity-limited supermoves; unlimited sequence moves are a different ruleset.
- Proof of legality and validity preservation, soundness of positive and negative answers, completeness, and termination of the unrestricted algorithm.
- Practical limits produce unknown with a reason. Malformed input produces an input error. Neither is an impossibility proof.

Other solitaire variants, alternative free-cell counts, shortest winning paths, graphical play, and a guarantee of solving every deal quickly are deferred. Standard FreeCell is the first coherent deliverable; the upstream to-do’s mention of similar games does not become an implicit promise to verify all variants. Acceptance of the upstream request remains the maintainers’ judgment.

## Result and trust contracts

**Winnable:** a validated path begins at the requested position, every step satisfies the move relation, and its final position is won.

**Unwinnable:** a checked set includes the requested position, is closed under every legal successor, and contains no won position. Reuse and generalize the existing induction argument.

**Unknown:** the practical search hit a state, time, memory, cancellation or other declared limit without establishing either answer. A truncated search is not a negative certificate unless the certificate checker independently establishes closure.

The algorithmic goal additionally requires a total decision procedure with proved equivalence to reachability. A generic certificate checker alone is a valuable milestone, but does not fulfill that goal.

Lean checks the general mathematical arguments. The specification remains the bridge to the real game; independent rule and deal checks are required. The baseline uses `native_decide` for large finite checks, adding native-compiler trust. Preserve that disclosure if retained. Kernel-only finite computation is an optional investigation, not an undisclosed requirement or a promise already met.

## Success criteria

1. Lean accepts the general validity, transition-enumeration, search-soundness, search-completeness and termination theorems without `sorry` or project-defined assumptions that assert the desired result.
2. The real CLI validates input, binds evidence to the exact requested board/rules, and distinguishes checked outcomes from unknown and errors.
3. Reproduce #11982 as unwinnable and winning paths for #1, #617 and #1941. Reject corrupt certificates and invalid paths. Independent differential evidence supplements, but never replaces, the general proofs.
4. A clean checkout with a pinned toolchain can build, run tests and reproduce the documented examples. State costs and any optional expensive checks honestly.
5. A separate adversarial review attacks specification fidelity, theorem scope, limits, parsing and practical execution before a release or a new upstream claim.

## What is not yet decided

Choose concrete data structures, certificate encoding, a finite-state bound or well-founded measure, and CLI syntax during implementation. Lean 4.35.0 is the verified starting toolchain, not a permanent ban on a justified upgrade. Prefer Std initially; add Mathlib only if it materially simplifies necessary proofs. Publish no performance promises before benchmarks. Public repository creation, licensing, and another external submission require subsequent user direction.
