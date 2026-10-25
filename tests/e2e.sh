#!/usr/bin/env bash
# End-to-end tests through the real command line. Run from the repository root
# after `lake build`. Works only in a fresh temporary directory, which it removes.
set -u
B="$(pwd)/.lake/build/bin/freecell"
W="$(mktemp -d "${TMPDIR:-/tmp}/freecell-e2e.XXXXXX")"
trap 'rm -rf "$W"' EXIT
pass=0; fail=0

expect() { # name expected-status actual-status [output-file pattern]
  local name=$1 want=$2 got=$3
  if [ "$got" != "$want" ]; then echo "FAIL $name: exit $got, expected $want"; fail=$((fail+1)); return; fi
  if [ $# -ge 5 ] && ! grep -q -- "$5" "$4"; then
    echo "FAIL $name: output lacks '$5'"; sed 's/^/   | /' "$4" | head -5; fail=$((fail+1)); return
  fi
  pass=$((pass+1))
}
G="$(pwd)/scripts/memguard.sh"
run() { "$G" "$B" "$@" >"$W/out" 2>&1; echo $?; }

# decided outcomes, evidence written and re-verified from disk
s=$(run solve --deal 11982 --certificate "$W/11982.cert"); expect "11982 unwinnable" 0 "$s" "$W/out" "unwinnable: every reachable position explored (84767 positions)"
s=$(run verify --deal 11982 "$W/11982.cert"); expect "11982 certificate accepted" 0 "$s" "$W/out" "accepted: the position is unwinnable"
s=$(run solve --deal 1 --certificate "$W/1.cert" --moves); expect "1 winnable" 0 "$s" "$W/out" "^winnable:"
s=$(run verify --deal 1 "$W/1.cert"); expect "1 certificate accepted" 0 "$s" "$W/out" "accepted: the position is winnable"
s=$(run solve --deal 1 --json); expect "json output" 0 "$s"
python3 -c 'import json,sys; d=json.load(open(sys.argv[1])); assert d["result"]=="winnable" and d["moveCount"]>0' "$W/out" \
  && pass=$((pass+1)) || { echo "FAIL json parse"; fail=$((fail+1)); }
s=$(run solve --deal 1 --json); expect "proposer labelled" 0 "$s" "$W/out" '"engine":"proposer"'
s=$(run solve --deal 1 --reference-only --json --certificate "$W/1r.cert"); expect "reference-only labelled" 0 "$s" "$W/out" '"engine":"reference"'
s=$(run verify --deal 1 "$W/1r.cert"); expect "reference-only certificate accepted" 0 "$s" "$W/out" "winnable"
s=$(run solve --deal 11982 --json); expect "unwinnable from reference" 0 "$s" "$W/out" '"engine":"reference"'
for g in 1 617 1941; do
  s=$(run verify --deal $g tests/fixtures/independent-win-$g.cert); expect "independent witness $g" 0 "$s" "$W/out" "winnable"
done

# wrong board
s=$(run verify --deal 2 "$W/1.cert"); expect "win certificate for another deal" 4 "$s" "$W/out" "different starting position"
s=$(run verify --deal 11981 "$W/11982.cert"); expect "loss certificate for another deal" 4 "$s" "$W/out" "different starting position"
# same evidence relabelled with the other deal's start line is still checked against the requested deal
sed "3s/.*/$(sed -n 3p "$W/1.cert" | sed 's/[\/&]/\\&/g')/" "$W/11982.cert" > "$W/relabel.cert"
s=$(run verify --deal 1 "$W/relabel.cert"); expect "relabelled closed set rejected" 4 "$s" "$W/out" "not a closed"

# tampering with winning paths
awk 'NR==6{next}{print}' "$W/1.cert" | sed "4s/winnable: \([0-9]*\)/winnable: $(( $(sed -n 4p "$W/1.cert" | cut -d' ' -f2) - 1 ))/" > "$W/t1.cert"
s=$(run verify --deal 1 "$W/t1.cert"); expect "move deleted" 4 "$s" "$W/out" "rejected"
sed '$d' "$W/1.cert" | sed "4s/winnable: \([0-9]*\)/winnable: $(( $(sed -n 4p "$W/1.cert" | cut -d' ' -f2) - 1 ))/" > "$W/t2.cert"
s=$(run verify --deal 1 "$W/t2.cert"); expect "last move deleted" 4 "$s" "$W/out" "does not end in a won position"
sed '$d' "$W/1.cert" > "$W/t3.cert"
s=$(run verify --deal 1 "$W/t3.cert"); expect "count mismatch" 4 "$s" "$W/out" "declares"
sed '2s/v1$/v2/' "$W/1.cert" > "$W/t4.cert"
s=$(run verify --deal 1 "$W/t4.cert"); expect "wrong rules id" 4 "$s" "$W/out" "expected 'rules"

# tampering with closed sets
n=$(sed -n 4p "$W/11982.cert" | cut -d' ' -f2)
awk 'NR==5{next}{print}' "$W/11982.cert" | sed "4s/.*/unwinnable: $((n-1))/" > "$W/l1.cert"
s=$(run verify --deal 11982 "$W/l1.cert"); expect "position deleted" 4 "$s" "$W/out" "not a closed"
{ sed "4s/.*/unwinnable: $((n+1))/" "$W/11982.cert"; echo "13.13.13.13||||||||"; } > "$W/l2.cert"
s=$(run verify --deal 11982 "$W/l2.cert"); expect "won position inserted" 4 "$s" "$W/out" "not a closed"
head -3 "$W/11982.cert" > "$W/l3.cert"; echo "unwinnable: 0" >> "$W/l3.cert"
s=$(run verify --deal 11982 "$W/l3.cert"); expect "empty closed set" 4 "$s" "$W/out" "not a closed"
head -c 1000 "$W/11982.cert" > "$W/l4.cert"
s=$(run verify --deal 11982 "$W/l4.cert"); expect "truncated file" 4 "$s" "$W/out" "rejected"
printf 'garbage\n' > "$W/l5.cert"
s=$(run verify --deal 11982 "$W/l5.cert"); expect "garbage certificate" 4 "$s" "$W/out" "rejected"

# invalid input
"$B" deal 1 > "$W/d1.txt"
s=$(run solve --position "$W/d1.txt"); expect "position file solves" 0 "$s" "$W/out" "winnable"
sed 's/JD/TC/' "$W/d1.txt" > "$W/dup.txt"
s=$(run solve --position "$W/dup.txt"); expect "duplicate card" 2 "$s" "$W/out" "duplicate card TC"
sed '$d' "$W/d1.txt" > "$W/seven.txt"
s=$(run solve --position "$W/seven.txt"); expect "seven columns" 2 "$s" "$W/out" "expected 8 columns"
sed 's/^Foundations: C-0/Foundations: C-A/' "$W/d1.txt" > "$W/overlap.txt"
s=$(run solve --position "$W/overlap.txt"); expect "foundation overlap" 2 "$s" "$W/out" "duplicate card AC"
sed 's/ 2D / XX /' "$W/d1.txt" > "$W/badcard.txt"
s=$(run solve --position "$W/badcard.txt"); expect "unknown card" 2 "$s" "$W/out" "invalid card 'XX'"
s=$(run solve --position "$W/missing-file.txt"); expect "missing file" 2 "$s" "$W/out" "cannot read"
s=$(run solve --deal 0); expect "deal 0" 2 "$s" "$W/out" "between 1 and 32000"
s=$(run solve --deal 32001); expect "deal 32001" 2 "$s" "$W/out" "between 1 and 32000"
s=$(run solve --deal 1 --bogus); expect "unknown option" 2 "$s" "$W/out" "unknown or incomplete option"
s=$(run solve --deal); expect "missing option value" 2 "$s" "$W/out" "unknown or incomplete option"
s=$(run frobnicate); expect "unknown command" 2 "$s" "$W/out" "unknown command"
printf 'Foundations: C-K D-K H-K S-K\n:\n:\n:\n:\n:\n:\n:\n:\n' > "$W/won.txt"
s=$(run solve --position "$W/won.txt" --max-positions 0); expect "won start decided under zero budget" 0 "$s" "$W/out" "winnable: 0 moves"

# budgets and cancellation: unknown, never an impossibility claim
s=$(run solve --deal 11982 --max-positions 0); expect "zero position budget" 3 "$s" "$W/out" "unknown: position limit"
s=$(run solve --deal 11982 --max-positions 1000); expect "small position budget" 3 "$s" "$W/out" "unknown: position limit"
grep -q "unwinnable" "$W/out" && { echo "FAIL budget output mentions unwinnable"; fail=$((fail+1)); }
s=$(run solve --deal 11982 --time-limit 0); expect "zero time limit" 3 "$s" "$W/out" "unknown: time limit"
s=$(run solve --deal 11982 --max-positions 10 --certificate "$W/none.cert"); expect "no certificate on unknown" 3 "$s"
[ ! -e "$W/none.cert" ] && pass=$((pass+1)) || { echo "FAIL certificate written for unknown"; fail=$((fail+1)); }
touch "$W/cancel"
s=$(run solve --deal 11982 --cancel-file "$W/cancel"); expect "pre-cancelled" 3 "$s" "$W/out" "unknown: cancelled"
rm "$W/cancel"
"$G" "$B" solve --deal 617 --cancel-file "$W/cancel" > "$W/out" 2>&1 & pid=$!
sleep 1; touch "$W/cancel"; wait $pid; s=$?
expect "cancelled while running" 3 "$s" "$W/out" "unknown: cancelled"
s=$(run solve --deal 11982 --json --max-positions 5); expect "json unknown" 3 "$s" "$W/out" '"result":"unknown"'

# review 0002 regressions
s=$(run solve --deal 11982 --max-positions 5); expect "tight position budget" 3 "$s" "$W/out" "unknown: position limit"
n=$(sed -n 's/.*after visiting \([0-9]*\) positions.*/\1/p' "$W/out")
[ -n "$n" ] && [ "$n" -le 30 ] && pass=$((pass+1)) || { echo "FAIL budget overshoot: $n"; fail=$((fail+1)); }
cp "$W/d1.txt" "$W/keep.txt"
s=$(run solve --position "$W/keep.txt" --certificate "$W/keep.txt"); expect "refuse to overwrite" 2 "$s" "$W/out" "already exists"
cmp -s "$W/d1.txt" "$W/keep.txt" && pass=$((pass+1)) || { echo "FAIL input overwritten"; fail=$((fail+1)); }
s=$(run solve --deal 1 --certificate "$W/no/such/dir/x.cert"); expect "unwritable certificate path" 1 "$s" "$W/out" "cannot write certificate"
s=$(run solve --deal 1 --json --certificate "$W/no/such/dir/y.cert"); expect "unwritable path json" 1 "$s" "$W/out" '"result":"error"'
s=$(run deals 0 0); expect "deals below range" 2 "$s" "$W/out" "deals expects"
s=$(run deals 5 1); expect "deals reversed" 2 "$s" "$W/out" "deals expects"
s=$(run solve --deal 1_1982); expect "underscore number" 2 "$s" "$W/out" "natural number"
s=$(run verify --deal 1 --certificate "$W/1.cert" "$W/1.cert"); expect "inapplicable option" 2 "$s" "$W/out" "does not apply"
s=$(run solve --deal 1 --deal 2); expect "repeated option" 2 "$s" "$W/out" "more than once"
s=$(run solve --deal 11982 --max-positions unlimited); expect "explicitly unlimited" 0 "$s" "$W/out" "unwinnable"
s=$(run solve --deal 1 --max-positions unbounded); expect "bad position limit" 2 "$s" "$W/out" "natural number"
s=$(run help); expect "default position cap documented" 0 "$s" "$W/out" "default 10000000"
s=$(run verify --position - -); expect "stdin twice" 2 "$s" "$W/out" "standard input"

echo "$pass passed, $fail failed"
[ "$fail" -eq 0 ]
