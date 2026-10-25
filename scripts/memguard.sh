#!/usr/bin/env bash
# Run a command under a memory cap. macOS does not enforce `ulimit -v`, so this polls.
#
# The command runs as the leader of its own process group. The guarded set is every
# process in that group plus every descendant of the command, so children that are
# reparented to launchd (their parent exited) are still counted and still killed.
# When the set's combined resident memory exceeds the cap, the whole set is killed
# (TERM, then KILL). INT, TERM and HUP sent to the guard are forwarded to the whole
# set, and anything the command leaves running when it exits is terminated too.
# Only a process that both leaves the group (setsid) and loses its parent between
# two polls can escape; nothing this repository runs does that.
#
# Usage: scripts/memguard.sh [-m MEGABYTES] COMMAND [ARGS...]
# The cap defaults to $FREECELL_MEM_MB, else 16384, and must be a positive integer.
# Exit status: the command's own; 137 if the guard killed it for memory; 2 for a bad
# cap or missing command (the command is then not started); 128+N if the guard was
# interrupted by signal N.
set -u
cap="${FREECELL_MEM_MB:-16384}"
if [ "${1:-}" = "-m" ]; then cap=${2:-}; shift 2 || shift $#; fi
case "$cap" in
  ''|*[!0-9]*|0) echo "memguard: the cap must be a positive whole number of megabytes, got '$cap'" >&2; exit 2 ;;
esac
[ $# -ge 1 ] || { echo "usage: memguard.sh [-m MB] COMMAND [ARGS...]" >&2; exit 2; }

# Start the command as its own process group leader (pgid = its pid).
perl -e 'setpgrp(0, 0) or die "setpgrp: $!"; exec { $ARGV[0] } @ARGV or die "exec $ARGV[0]: $!\n"' -- "$@" &
root=$!
case "$root" in ''|*[!0-9]*|0|1) echo "memguard: could not start the command" >&2; exit 2 ;; esac

# Guarded PIDs (pgid == root, or descended from root) and their total RSS in KB.
members() {
  ps -A -o pid=,ppid=,pgid=,rss= | awk -v root="$root" '
    { pid[NR]=$1; ppid[NR]=$2; pg[NR]=$3; rss[NR]=$4 }
    END {
      for (i=1;i<=NR;i++) if (pid[i]==root || pg[i]==root) inside[pid[i]]=1
      changed=1
      while (changed) { changed=0
        for (i=1;i<=NR;i++) if (!(pid[i] in inside) && (ppid[i] in inside)) { inside[pid[i]]=1; changed=1 } }
      total=0; list=""
      for (i=1;i<=NR;i++) if (pid[i] in inside) { total+=rss[i]; list=list" "pid[i] }
      print total list }'
}

signal_members() { # signal the guarded PIDs; never 0, negative or this script's own PID
  local sig=$1 kb p
  local -a pids
  read -r kb pids_line <<<"$(members)"
  read -r -a pids <<<"${pids_line:-}"
  for p in "${pids[@]+"${pids[@]}"}"; do
    case "$p" in ''|*[!0-9]*|0) continue ;; esac
    [ "$p" -eq $$ ] && continue
    kill "-$sig" "$p" 2>/dev/null
  done
}

kill_all() { # signal every guarded process, then KILL whatever is left
  local sig=$1
  kill "-$sig" -- "-$root" 2>/dev/null
  signal_members "$sig"
  sleep 0.5
  kill -KILL -- "-$root" 2>/dev/null
  signal_members KILL
}

on_signal() { kill_all TERM; wait "$root" 2>/dev/null; exit $((128 + $1)); }
trap 'on_signal 2' INT
trap 'on_signal 15' TERM
trap 'on_signal 1' HUP

polls=0
status=
while :; do
  read -r kb pids <<<"$(members)"
  if [ "${kb:-0}" -gt $((cap * 1024)) ]; then
    echo "memguard: command $root and its processes used $((kb / 1024)) MB > cap $cap MB; killing PIDs$( [ -n "$pids" ] && echo " $pids")" >&2
    kill_all TERM
    wait "$root" 2>/dev/null
    exit 137
  fi
  if [ -z "$status" ] && ! kill -0 "$root" 2>/dev/null; then
    wait "$root"; status=$?
  fi
  if [ -n "$status" ]; then
    # the command has exited; stop anything it left behind
    read -r kb pids <<<"$(members)"
    if [ -n "${pids:-}" ]; then
      echo "memguard: command exited and left PIDs $pids running; terminating them" >&2
      kill_all TERM
    fi
    exit "$status"
  fi
  # poll quickly at first so short commands are not delayed
  if [ "$polls" -lt 40 ]; then sleep 0.02; polls=$((polls + 1)); else sleep 0.5; fi
done
