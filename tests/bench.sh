#!/usr/bin/env bash
# Benchmark: solve deals FROM..TO with a per-deal time limit; one JSON line per deal.
# Usage: tests/bench.sh FROM TO SECONDS [BINARY] > results.jsonl
# Each solve runs under scripts/memguard.sh (FREECELL_MEM_MB, default 16 GB).
G="$(cd "$(dirname "$0")/.." && pwd)/scripts/memguard.sh"
B="${4:-$(pwd)/.lake/build/bin/freecell}"
for g in $(seq "$1" "$2"); do
  t0=$(python3 -c 'import time;print(time.time())')
  out=$("$G" "$B" solve --deal "$g" --time-limit "$3" --json 2>&1); code=$?
  t1=$(python3 -c 'import time;print(time.time())')
  echo "{\"deal\":$g,\"exit\":$code,\"seconds\":$(python3 -c "print(round($t1-$t0,3))"),\"output\":$out}"
done
