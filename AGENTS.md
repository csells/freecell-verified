# FreeCell Verified — agent guide

Before implementation, read `specs/vision/verified-freecell.md`, `specs/plans/0001-verified-freecell-solver.md`, and `specs/references/freecell-11982/README.md`. For the originating task and its authority, read `specs/handoff.md`.

- Work inside this repository. Treat the blog repository and copied reference evidence as read-only inputs. Preserve original reference files; derive new implementation files from copies.
- Preserve user data and experiment output. Test in fresh scratch locations. Kill only processes this task started, by explicit PID; never kill applications or use name patterns.
- Keep internal decisions, plans and review evidence under `specs/`. Update milestone status only when its acceptance evidence exists.
- Use red/green tests for executable behavior and Lean-checked theorem statements for proof obligations. Record failures explicitly; limits and interruption yield unknown, not unwinnable.
- Report the actual axiom dependencies and specification scope. `sorry`, unproved axioms and successful finite test suites cannot stand in for the promised general theorems.
- Resolve routine technical choices from evidence. When a genuine user decision is necessary, ask and wait for the explicit answer; elapsed time is not approval.
- Use independent adversarial agents when useful for rule fidelity, proof soundness, or executable/certificate boundaries. Keep their inputs and conclusions explicit.
- Creating this local project does not authorize a GitHub repository, deployment, or upstream submission. Do not append AI attribution to commits or PRs.
