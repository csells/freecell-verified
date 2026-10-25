#!/usr/bin/env bash
# Slower reproduction checks (about 15 minutes). Needs a C compiler for deal parity.
set -euo pipefail
cd "$(dirname "$0")/.."
# Every command runs under a memory cap (FREECELL_MEM_MB, default 16 GB).
G=scripts/memguard.sh
$G lake build
W="$(mktemp -d "${TMPDIR:-/tmp}/freecell-long.XXXXXX")"
trap 'rm -rf "$W"' EXIT
echo "== original #11982 proof (expect 84767 and its native_decide axiom)"
$G lake env lean specs/references/freecell-11982/FreeCell11982.lean | tee "$W/ref.log"
diff specs/references/freecell-11982/original-run.log "$W/ref.log" && echo "identical to original-run.log"
echo "== deal corollaries: native_decide results and the kernel-checked sample"
$G lake build Examples
$G lake env lean tests/ExamplesAxioms.lean | python3 tests/tools/check_axioms.py
echo "== the 32,000-deal data regenerates from the archived solver output"
E=specs/evidence/ms32000
mkdir -p "$W/regen/Ms32000"
python3 tests/tools/gen_bulk.py "$W/regen/Ms32000" <(gzip -dc $E/pass1.jsonl.gz) \
  <(gzip -dc $E/pass2.jsonl.gz) <(gzip -dc $E/pass3-fcsolve.jsonl.gz)
diff -r "$W/regen/Ms32000" Examples/Ms32000
cmp "$W/regen/Ms32000.lean" Examples/Ms32000.lean
cmp "$W/regen/Ms32000Kernel.lean" Examples/Ms32000Kernel.lean
echo "regenerated files identical"
echo "== tamper control: a chunk missing one move must not check"
python3 - "$W/Tamper.lean" <<'PY'
import sys
s = open('Examples/Ms32000/Chunk07.lean').read().replace('namespace FreeCell.Examples.Ms32000\n',
    'namespace FreeCell.Examples.Ms32000Tamper\n').replace('end FreeCell.Examples.Ms32000\n',
    'end FreeCell.Examples.Ms32000Tamper\n')
i = s.index('def data07 : String := "') + len('def data07 : String := "')
j = s.index('\\n', i)
open(sys.argv[1], 'w').write(s[:j - 2] + s[j:])
PY
if $G lake env lean "$W/Tamper.lean" > "$W/tamper.log" 2>&1; then
  echo "tampered chunk was accepted"; exit 1
fi
if ! grep -q "native_decide\` evaluated that the proposition" "$W/tamper.log"; then
  echo "tampered chunk failed for another reason:"; cat "$W/tamper.log"; exit 1
fi
echo "tampered chunk rejected by native_decide"
echo "== deal layout parity with Freecell Solver's generator, deals 1-32000"
cc -O2 -I specs/references/fc-solve-5c057b7 -I tests/parity/stub -o "$W/ms_deals" tests/parity/ms_deals.c
"$W/ms_deals" 1 32000 > "$W/upstream.txt"
$G .lake/build/bin/freecell deals 1 32000 > "$W/lean.txt"
cmp "$W/upstream.txt" "$W/lean.txt" && echo "32000 deals identical"
