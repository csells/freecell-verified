#!/usr/bin/env bash
# Fast checks (a few minutes): build, forbidden constructs, axioms, Lean tests, CLI tests,
# memory-guard tests.
set -euo pipefail
cd "$(dirname "$0")/.."
# Every command runs under a memory cap (FREECELL_MEM_MB, default 16 GB).
G=scripts/memguard.sh
$G tests/memguard-test.sh
$G lake build

# Forbidden constructs: none in the library or CLI; only native_decide in Examples.
# The checker itself must flag every fixture under tests/fixtures/forbidden/flag.
python3 tests/tools/forbidden.py FreeCell FreeCell.lean Main.lean
python3 tests/tools/forbidden.py --allow-native Examples
python3 tests/tools/forbidden.py tests/fixtures/forbidden/pass
for f in tests/fixtures/forbidden/flag/*.lean; do
  if python3 tests/tools/forbidden.py "$f" > /dev/null; then
    echo "forbidden-construct checker missed $f"; exit 1
  fi
done
echo "forbidden constructs: none (checker flags all $(ls tests/fixtures/forbidden/flag/*.lean | wc -l | tr -d ' ') fixtures)"

ax="${TMPDIR:-/tmp}/freecell-axioms.$$"
trap 'rm -f "$ax"' EXIT
$G lake env lean tests/Axioms.lean > "$ax"
if grep -E "depends on axioms|does not depend on any axioms" "$ax" \
    | grep -vE "depends on axioms: \[(propext(, Classical.choice)?, )?Quot.sound\]|depends on axioms: \[propext\]|does not depend on any axioms"; then
  echo "unexpected axiom dependency"; exit 1
fi
want=$(grep -c '^#print axioms' tests/Axioms.lean)
got=$(grep -cE "depends on axioms|does not depend on any axioms" "$ax" || true)
[ "$want" -eq "$got" ] || { echo "axiom report covers $got of $want theorems"; exit 1; }
echo "axioms: only propext, Classical.choice, Quot.sound ($got theorems)"

$G lake build tests
$G .lake/build/bin/tests
$G tests/e2e.sh
