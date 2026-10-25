#!/usr/bin/env bash
# Fast checks (about a minute): build, forbidden constructs, axioms, Lean tests, CLI tests.
set -euo pipefail
cd "$(dirname "$0")/.."
# Every command runs under a memory cap (FREECELL_MEM_MB, default 16 GB).
G=scripts/memguard.sh
$G lake build
if grep -rnE '\bsorry\b|\badmit\b|native_decide|implemented_by|@\[extern|@\[csimp|\baxiom\b|^\s*(private |protected |noncomputable )*(partial|unsafe|opaque)\b|\bunsafe\b|skipKernelTC|debug\.skip' \
    FreeCell FreeCell.lean Main.lean; then
  echo "forbidden construct in library or CLI sources"; exit 1
fi
$G lake env lean tests/Axioms.lean > "${TMPDIR:-/tmp}/freecell-axioms.$$"
if grep -vE "depends on axioms: \[propext(, Classical.choice)?, Quot.sound\]" "${TMPDIR:-/tmp}/freecell-axioms.$$" \
    | grep "depends on axioms"; then
  echo "unexpected axiom dependency"; rm -f "${TMPDIR:-/tmp}/freecell-axioms.$$"; exit 1
fi
rm -f "${TMPDIR:-/tmp}/freecell-axioms.$$"
echo "axioms: only propext, Classical.choice, Quot.sound"
$G lake build tests
$G .lake/build/bin/tests
$G tests/e2e.sh
