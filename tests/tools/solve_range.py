"""Solve Microsoft deals FROM..TO in parallel with the freecell CLI; resumable.

Untrusted batch glue. Appends one JSON line per deal to OUT ({"deal", "exit", "seconds",
"output"}), skipping deals already recorded there with a decided result (exit 0 and result
"winnable" or "unwinnable"). A torn last line from an interrupted run is ignored. With
--only-from, only deals not decided in that earlier file are run (including deals it lacks).
Every solve runs under scripts/memguard.sh. Progress lines go to stderr.

Usage: python3 tests/tools/solve_range.py FROM TO OUT [--workers N] [--time-limit S]
       [--mem-mb MB] [--binary PATH] [--proposer-budget N] [--max-positions N]
       [--only-from EARLIER.jsonl] [--full-priority]
"""
import argparse, json, os, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor, as_completed

root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
ap = argparse.ArgumentParser()
ap.add_argument('lo', type=int); ap.add_argument('hi', type=int); ap.add_argument('out')
ap.add_argument('--workers', type=int, default=12)
ap.add_argument('--time-limit', type=int, default=20)
ap.add_argument('--mem-mb', type=int, default=4096)
ap.add_argument('--binary', default=os.path.join(root, '.lake/build/bin/freecell'))
ap.add_argument('--proposer-budget', type=int, default=None)
ap.add_argument('--max-positions', type=int, default=None)
ap.add_argument('--only-from', default=None, help='run only deals this earlier JSONL did not decide')
ap.add_argument('--full-priority', action='store_true', help='do not lower CPU priority')
a = ap.parse_args()
if not a.full_priority:
    os.nice(19)  # workers inherit this: leave the machine responsive for other work

def decided(path):
    """Deals with a decided result in a results file; unreadable lines are skipped."""
    out = set()
    for n, line in enumerate(open(path), 1):
        try:
            r = json.loads(line)
        except ValueError:
            print(f'{path}:{n}: ignoring an unreadable line', file=sys.stderr)
            continue
        if r.get('exit') == 0 and r.get('output', {}).get('result') in ('winnable', 'unwinnable'):
            out.add(r['deal'])
    return out

done = decided(a.out) if os.path.exists(a.out) else set()
todo = [g for g in range(a.lo, a.hi + 1) if g not in done]
if a.only_from:
    earlier = decided(a.only_from)
    todo = [g for g in todo if g not in earlier]
print(f'{len(done)} already decided, {len(todo)} to run', file=sys.stderr, flush=True)

def solve(g):
    cmd = [os.path.join(root, 'scripts/memguard.sh'), '-m', str(a.mem_mb), a.binary, 'solve',
           '--deal', str(g), '--moves', '--json', '--time-limit', str(a.time_limit)]
    if a.proposer_budget is not None: cmd += ['--proposer-budget', str(a.proposer_budget)]
    if a.max_positions is not None: cmd += ['--max-positions', str(a.max_positions)]
    t0 = time.time()
    p = subprocess.run(cmd, capture_output=True, text=True)
    try: out = json.loads(p.stdout)
    except ValueError: out = {'result': 'error', 'stdout': p.stdout[-500:], 'stderr': p.stderr[-500:]}
    return {'deal': g, 'exit': p.returncode, 'seconds': round(time.time() - t0, 3), 'output': out}

counts = {}
if os.path.exists(a.out) and os.path.getsize(a.out) and not open(a.out, 'rb').read().endswith(b'\n'):
    with open(a.out, 'a') as f: f.write('\n')  # terminate a torn last line before appending
with open(a.out, 'a') as f, ThreadPoolExecutor(a.workers) as ex:
    futs = [ex.submit(solve, g) for g in todo]
    for i, fut in enumerate(as_completed(futs), 1):
        r = fut.result()
        f.write(json.dumps(r) + '\n'); f.flush()
        res = r['output'].get('result', '?')
        counts[res] = counts.get(res, 0) + 1
        if i % 100 == 0 or i == len(todo) or res != 'winnable':
            print(f'[{i}/{len(todo)}] ({i * 100 // max(1, len(todo))}%) deal {r["deal"]} {res} '
                  f'{r["seconds"]}s  totals {counts}', file=sys.stderr, flush=True)
