# Reference evidence: FreeCell #11982

Immutable starting material copied from the blog project on 2026-10-25. `manifest.json` records source paths, hashes and the published blog commit. These files are not an implementation of the new general solver.

`FreeCell11982.lean` is the published 151-line proof, pinned in the [blog repository](https://github.com/csells/sb8/blob/1fa642c1ad1cb9e96c9535773ddc021fe6a17271/content/public/freecell-11982/FreeCell11982.lean). Run with Lean4.35.0. The earlier audit ran identical executable code; the published copy corrects only a header comment about the native axiom. Thus the audit source hash d476cb6e3e778179398a919760fa9e0417aea6e195139ce95632027ae93a53a5 differs from this copy’s manifest hash. The logs are prior-run evidence, not a fresh execution in this project.

- `original-run.log`: exact successful original output, including 84,767 and the actual axiom list.
- `negative-controls.log`: valid certificate accepted; damaged/empty/winning-state and truncated-search controls rejected.
- `witness-replay.log`: independent paths accepted by exact Lean moves for #1 (115 moves), #617 (144) and #1941 (106); altered paths rejected.
- `environment.json`: original review toolchain/hardware and invocation. Temporary paths in this historical receipt are not required runtime dependencies.
- `independent-baseline.json`: separate Python rules implementation found 84,767 states, 314,366 edges, at most two cards home, eight frozen cards and eight states exposing QC. Its columns are stored bottom-to-top; the Lean file stores exposed cards at the head. Do not confuse these orientations.

The complete local review, programs and original experiment receipts remain at `/Users/csells/Code/csells/sb8/specs/reviews/freecell-adversarial-20261025/`. Read them there if needed; do not modify that project. The current handoff needs no access to its old temporary toolchain. An independent oracle for Microsoft deal generation was [fc-solve revision5c057b7](https://github.com/shlomif/fc-solve/blob/5c057b70548510612feb45616a45705a5cd9735b/fc-solve/source/gen_ms_boards__rand.h).

Important boundary: existing `cert_sound` establishes the closed-set argument for a fixed starting deal. It neither proves general solver completeness nor proves that its fuel is sufficient for arbitrary inputs. `native_decide` introduces the disclosed compiler trust. Mathematical proof of generic algorithm correctness and empirical comparison to actual game rules are separate obligations.
