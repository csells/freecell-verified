# Handoff: FreeCell Verified

## Mission and authority

Develop the general standard-FreeCell solver described in this repository’s vision and plan. Chris asked to create this separate local project after publishing a one-deal proof, and will use this handoff to start implementation. This repository was created as a planning scaffold only; no general solver has been implemented or tested. When Chris supplies this prompt as the implementation request, proceed through the plan locally. Public repository creation, publication, licensing decisions and external submissions are not covered by the scaffold request.

Work only in `/Users/csells/code/csells/freecell-verified`. The filesystem treats `Code` and `code` as the same directory on this Mac. Do not alter the published blog repository or its open PR.

## Read first, in order

1. `AGENTS.md` — preservation, verification, scope and collaboration rules.
2. `specs/vision/verified-freecell.md` — success contracts and exclusions.
3. `specs/plans/0001-verified-freecell-solver.md` — complete work list M0–M6 and acceptance evidence.
4. `specs/references/freecell-11982/README.md` — provenance, prior verification and limitations.
5. `specs/references/freecell-11982/FreeCell11982.lean` — seed rules, checkCert, cert_sound and fuel-limited search.

## Established context

Chris’s article is https://sellsbrothers.com/freecell-11982-proof . The single-file proof is https://sellsbrothers.com/public/freecell-11982/FreeCell11982.lean . Upstream PR https://github.com/shlomif/fc-solve/pull/180 links that specific result; it does not submit or claim a general solver. Chris explicitly chose a single blog-hosted file for the article. This new general-solver project is separate and does not reverse that decision.

The old proof uses a trusted game specification, an untrusted DFS with fuel, a finite closure checker evaluated by native_decide, and an induction theorem. It proves #11982 unwinnable, not the search algorithm correct for arbitrary deals. Its Nat/List representation admits malformed states; simply replacing 11982 with an argument does not establish finite validity or total search correctness.

A thorough review found no blocking mathematical defect within that proof’s model and native-compiler trust boundary. Exact retained output and independent semantic evidence are copied beside the seed. The review’s prototype outputs are evidence, not tests to count as passing in this new project.

## First execution slice

Reproduce M0 under pinned Lean4.35.0, then implement the valid state model and declarative/executable move bridge in M1. Reuse the closure argument, not the assumption that existing structures are already suitably bounded. Work toward M2–M6 rather than stopping after generic certificate checking. Use proved results and actual end-to-end runs for acceptance; if a milestone is incomplete, leave it explicitly incomplete.

Expected baseline reproduction command after bootstrapping Lake:

    lake env lean specs/references/freecell-11982/FreeCell11982.lean

Expected count: 84767. Expected final axiom dependencies: propext, Classical.choice, Quot.sound, certificate_ok._native.native_decide.ax_1_1. The copied negative-controls.log records CERT_VALID true and false for DELETE_DEAL, DELETE_FIRST, DELETE_LAST, INSERT_WIN, EMPTY_CERT, FUEL_ZERO and FUEL_ONE. Recreate meaningful controls against new code rather than relabeling these old logs as fresh verification.

No unresolved user questions are pending. The plan’s data structures, certificate format and exact CLI syntax are engineering choices to resolve from evidence. Standard FreeCell is the proposed first deliverable; document deferred variants and do not claim the entire upstream request has been accepted by maintainers. Carry all safety and evidence rules in AGENTS.md through the work, and ask only for genuine decisions beyond the established scope.
