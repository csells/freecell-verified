#!/usr/bin/env bash
# Slower reproduction checks (a few minutes). Needs a C compiler for deal parity.
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
echo "== deal corollaries via native_decide"
$G lake build Examples
echo "== deal layout parity with Freecell Solver's generator, deals 1-32000"
cc -O2 -I specs/references/fc-solve-5c057b7 -I tests/parity/stub -o "$W/ms_deals" tests/parity/ms_deals.c
"$W/ms_deals" 1 32000 > "$W/upstream.txt"
$G .lake/build/bin/freecell deals 1 32000 > "$W/lean.txt"
cmp "$W/upstream.txt" "$W/lean.txt" && echo "32000 deals identical"
