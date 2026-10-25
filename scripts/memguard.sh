#!/usr/bin/env bash
# Run a command, killing it (and only its own descendants, by PID) if their combined
# resident memory exceeds a cap. macOS does not enforce `ulimit -v`, so this polls.
# Usage: scripts/memguard.sh [-m MEGABYTES] COMMAND [ARGS...]
# The cap defaults to $FREECELL_MEM_MB, else 16384. Exit status is the command's,
# or 137 if the guard killed it.
set -u
cap="${FREECELL_MEM_MB:-16384}"
if [ "${1:-}" = "-m" ]; then cap=$2; shift 2; fi
[ $# -ge 1 ] || { echo "usage: memguard.sh [-m MB] COMMAND [ARGS...]" >&2; exit 2; }

"$@" & root=$!

# PIDs of root and all its descendants, with their total RSS in KB.
tree() {
  ps -A -o pid=,ppid=,rss= | awk -v root="$root" '
    { pid[NR]=$1; ppid[NR]=$2; rss[NR]=$3 }
    END {
      inside[root]=1; changed=1
      while (changed) { changed=0
        for (i=1;i<=NR;i++) if (!(pid[i] in inside) && (ppid[i] in inside)) { inside[pid[i]]=1; changed=1 } }
      total=0; list=""
      for (i=1;i<=NR;i++) if (pid[i] in inside) { total+=rss[i]; list=list" "pid[i] }
      print total list }'
}

trap 'kill -TERM $root 2>/dev/null' INT TERM
while kill -0 "$root" 2>/dev/null; do
  set -- $(tree)
  kb=${1:-0}; shift || true
  if [ "$kb" -gt $((cap * 1024)) ]; then
    echo "memguard: process tree of $root used $((kb / 1024)) MB > cap $cap MB; killing PIDs $*" >&2
    kill -TERM "$@" 2>/dev/null; sleep 1; kill -KILL "$@" 2>/dev/null
    wait "$root" 2>/dev/null
    exit 137
  fi
  # poll quickly at first so short commands are not delayed
  if [ "${polls:=0}" -lt 40 ]; then sleep 0.02; polls=$((polls + 1)); else sleep 0.5; fi
done
wait "$root"
