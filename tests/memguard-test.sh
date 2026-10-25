#!/usr/bin/env bash
# Tests for scripts/memguard.sh. Allocations stay small (at most ~150 MB) so a broken
# guard cannot hurt the machine. Works in a fresh temporary directory, which it removes.
set -u
G="$(cd "$(dirname "$0")/.." && pwd)/scripts/memguard.sh"
W="$(mktemp -d "${TMPDIR:-/tmp}/memguard-test.XXXXXX")"
trap 'rm -rf "$W"' EXIT
pass=0; fail=0
ok() { pass=$((pass+1)); }
bad() { echo "FAIL $1"; fail=$((fail+1)); }
alive() { [ -f "$1" ] && kill -0 "$(cat "$1")" 2>/dev/null; }

# alloc.py MB PIDFILE OUTFILE: write own pid, allocate MB in 10 MB steps, hold 2 s, report
cat > "$W/alloc.py" <<'EOF'
import os, sys, time
mb, pidfile, out = int(sys.argv[1]), sys.argv[2], sys.argv[3]
open(pidfile, 'w').write(str(os.getpid()))
b = []
for _ in range(mb // 10): b.append(bytearray(10 * 1024 * 1024)); time.sleep(0.03)
time.sleep(2)
open(out, 'w').write('finished')
EOF
A="python3 $W/alloc.py"

"$G" sh -c 'exit 7'; [ $? -eq 7 ] && ok || bad "exit status passed through"
"$G" true; [ $? -eq 0 ] && ok || bad "success passed through"

"$G" -m 60 $A 150 "$W/p1" "$W/o1" 2>"$W/e1"; s=$?
[ $s -eq 137 ] && [ ! -e "$W/o1" ] && grep -q "memguard:" "$W/e1" && ok || bad "direct child killed over cap (exit $s)"

"$G" -m 200 $A 50 "$W/p2" "$W/o2"; s=$?
[ $s -eq 0 ] && [ -e "$W/o2" ] && ok || bad "under the cap runs to completion (exit $s)"

# a grandchild whose parent exits at once (reparented to launchd) is still guarded
"$G" -m 60 sh -c "($A 150 $W/p3 $W/o3 &) ; sleep 3" 2>"$W/e3"; s=$?
sleep 0.5
[ $s -eq 137 ] && [ ! -e "$W/o3" ] && ! alive "$W/p3" && ok || bad "detached grandchild killed over cap (exit $s)"

# a background process left running when the command exits is terminated
"$G" -m 500 sh -c "($A 20 $W/p4 $W/o4 &) ; sleep 0.3" 2>"$W/e4"; s=$?
sleep 0.5
[ $s -eq 0 ] && [ ! -e "$W/o4" ] && ! alive "$W/p4" && ok || bad "leftover process terminated at exit (exit $s)"

# bad caps are refused before the command starts
for c in abc 0 0.5 -5 ''; do
  "$G" -m "$c" touch "$W/started" 2>/dev/null; s=$?
  [ $s -eq 2 ] && [ ! -e "$W/started" ] && ok || bad "cap '$c' refused (exit $s)"
done
FREECELL_MEM_MB=junk "$G" touch "$W/started" 2>/dev/null; s=$?
[ $s -eq 2 ] && [ ! -e "$W/started" ] && ok || bad "bad FREECELL_MEM_MB refused (exit $s)"

# TERM and INT to the guard reach grandchildren
for sig in TERM INT; do
  rm -f "$W/p5" "$W/o5"
  # background jobs of a script start with SIGINT ignored; restore it, as for a terminal Ctrl-C
  perl -e '$SIG{INT} = "DEFAULT"; exec @ARGV' "$G" -m 500 sh -c "$A 20 $W/p5 $W/o5; sleep 30" & g=$!
  for _ in $(seq 50); do [ -s "$W/p5" ] && break; sleep 0.1; done
  kill -$sig $g; wait $g; s=$?
  sleep 0.5
  [ $s -ge 129 ] && ! alive "$W/p5" && [ ! -e "$W/o5" ] && ok || bad "$sig reaches grandchildren (exit $s)"
done

# the guard must never signal its caller (regression: an empty member list once became `kill 0`)
out=$(sh -c "\"$G\" -m 60 $A 150 $W/p6 $W/o6 2>/dev/null; echo caller-alive")
[ "$out" = "caller-alive" ] && ok || bad "caller survives a kill"
out=$(sh -c "\"$G\" -m 500 sh -c '($A 20 $W/p7 $W/o7 &); sleep 0.3' 2>/dev/null; echo caller-alive")
[ "$out" = "caller-alive" ] && ok || bad "caller survives leftover cleanup"

# short commands are not delayed much
t0=$(python3 -c 'import time; print(time.time())')
"$G" true
t1=$(python3 -c 'import time; print(time.time())')
python3 -c "import sys; sys.exit(0 if $t1 - $t0 < 0.5 else 1)" && ok || bad "short command overhead"

echo "$pass passed, $fail failed"
[ "$fail" -eq 0 ]
