"""Turn Freecell Solver solutions into freecell-verified single-card move lists.

Untrusted glue. For each deal it runs `freecell deal N`, solves the board with fc-solve
(`-p -t -sam`, which prints the position after every move), derives each move from the
difference between consecutive positions, and expands multi-card moves into single-card
moves through the free cells and empty columns. The resulting move list is only a
proposal. Each one is written as a certificate and checked with `freecell verify` (the
proved `checkWin`); only an accepted list is recorded as winnable (exit 0). The Lean build
of the bulk theorem checks every list again.

Writes JSON lines in the format of solve_range.py, with "engine": "fc-solve".
Usage: python3 tests/tools/fcsolve_moves.py FC_SOLVE FREECELL OUT.jsonl DEAL [DEAL ...]
"""
import json, os, re, subprocess, sys, tempfile

RANKS, SUITS = 'A23456789TJQK', 'CDHS'
CARD = re.compile(r'\b([A23456789TJQK]|10)([CDHS])\b')

def parse_card(r, s):
    return (RANKS.index('T' if r == '10' else r) + 1, SUITS.index(s))

def name(c):
    return RANKS[c[0] - 1] + SUITS[c[1]]

def red(c):
    return c[1] in (1, 2)

def parse_positions(text):
    """Every position block printed by fc-solve -p -t -sam, in order."""
    out = []
    for block in re.split(r'\n\s*\n', text):
        lines = [l for l in block.splitlines() if l.strip()]
        if not lines or not lines[0].startswith('Foundations:'):
            continue
        home = [0] * 4
        for suit, rank in re.findall(r'([HCDS])-(\w+)', lines[0]):
            home[SUITS.index(suit)] = 0 if rank == '0' else RANKS.index('T' if rank == '10' else rank) + 1
        cells = sorted(parse_card(*m) for m in CARD.findall(lines[1].split(':', 1)[1]))
        cols = [[parse_card(*m) for m in CARD.findall(l[1:])] for l in lines[2:10]]
        assert len(cols) == 8, block
        out.append((cols, cells, home))
    return out

class Game:
    def __init__(self, pos):
        cols, cells, home = pos
        self.cols = [list(c) for c in cols]; self.cells = list(cells); self.home = list(home)
        self.moves = []

    def snapshot(self):
        return (self.cols, sorted(self.cells), self.home)

    def col_to_cell(self, i):
        assert self.cols[i] and len(self.cells) < 4
        c = self.cols[i].pop(); self.cells.append(c); self.moves.append(f'c{i + 1} f')
        return c

    def cell_to_col(self, c, j):
        self.cells.remove(c); self.put(c, j); self.moves.append(f'f:{name(c)} c{j + 1}')

    def col_to_col(self, i, j):
        c = self.cols[i].pop(); self.put(c, j); self.moves.append(f'c{i + 1} c{j + 1}')

    def put(self, c, j):
        if self.cols[j]:
            p = self.cols[j][-1]
            assert p[0] == c[0] + 1 and red(p) != red(c), (name(c), name(p))
        self.cols[j].append(c)

    def home_from_col(self, i):
        c = self.cols[i].pop(); self.go_home(c); self.moves.append(f'c{i + 1} h')

    def home_from_cell(self, c):
        self.cells.remove(c); self.go_home(c); self.moves.append(f'f:{name(c)} h')

    def go_home(self, c):
        assert self.home[c[1]] + 1 == c[0]
        self.home[c[1]] = c[0]

    def run(self, k, i, j, temps):
        """Move the top k cards of column i to column j using cells and the empty columns temps."""
        f = 4 - len(self.cells)
        if k <= f + 1:
            parked = [self.col_to_cell(i) for _ in range(k - 1)]
            self.col_to_col(i, j)
            for c in reversed(parked):
                self.cell_to_col(c, j)
            return
        assert temps, f'run of {k} does not fit'
        e, rest = temps[0], temps[1:]
        m = min((f + 1) * 2 ** len(rest), k - 1)
        self.run(m, i, e, rest)
        self.run(k - m, i, j, rest)
        self.run(m, e, j, rest)

    def apply(self, a, b):
        (ca, fa, ha), (cb, fb, hb) = a, b
        lost = [i for i in range(8) if len(cb[i]) < len(ca[i])]
        gained = [j for j in range(8) if len(cb[j]) > len(ca[j])]
        cell_out = [c for c in fa if c not in fb]
        if hb != ha:
            if lost: self.home_from_col(lost[0])
            else: self.home_from_cell(cell_out[0])
        elif lost and gained:
            i, j = lost[0], gained[0]
            k = len(ca[i]) - len(cb[i])
            temps = [e for e in range(8) if e not in (i, j) and not self.cols[e]]
            self.run(k, i, j, temps)
        elif lost:
            self.col_to_cell(lost[0])
        else:
            self.cell_to_col(cell_out[0], gained[0])
        assert self.snapshot() == (cb, fb, hb), 'simulation diverged from fc-solve'

def solve(fc_solve, freecell, deal):
    board = subprocess.run([freecell, 'deal', str(deal)], capture_output=True, text=True, check=True).stdout
    with tempfile.NamedTemporaryFile('w', suffix='.board', delete=False) as f:
        f.write(board)
    try:
        p = subprocess.run([fc_solve, '-p', '-t', '-sam', f.name], capture_output=True, text=True,
                           env={**os.environ, 'FREECELL_SOLVER_QUIET': '1'}, timeout=600)
    finally:
        os.unlink(f.name)
    if 'This game is solveable.' not in p.stdout:
        return {'result': 'unknown', 'reason': 'fc-solve: ' + p.stdout.strip().splitlines()[-1:][0]}
    pos = parse_positions(p.stdout)
    g = Game(pos[0])
    for a, b in zip(pos, pos[1:]):
        g.apply(a, b)
    if g.home != [13] * 4:
        raise ValueError('converted moves do not end in a won position')
    verdict = verify(freecell, deal, g.moves)
    if verdict != 'accepted':
        return {'result': 'error', 'error': 'freecell verify rejected the converted moves: ' + verdict}
    return {'result': 'winnable', 'engine': 'fc-solve', 'verified': True,
            'moveCount': len(g.moves), 'moves': g.moves}

def verify(freecell, deal, moves):
    """Check a move list with the proved checker via `freecell verify`; 'accepted' or the reason."""
    start = subprocess.run([freecell, 'deals', str(deal), str(deal)], capture_output=True, text=True,
                           check=True).stdout.split(' ', 1)[1].strip()
    cert = ('freecell-verified certificate v1\nrules: standard-freecell/single-card/4-cells/v1\n'
            f'start: {start}\nwinnable: {len(moves)}\n' + ''.join(m + '\n' for m in moves))
    with tempfile.NamedTemporaryFile('w', suffix='.cert', delete=False) as f:
        f.write(cert)
    try:
        v = subprocess.run([freecell, 'verify', '--deal', str(deal), f.name], capture_output=True, text=True)
    finally:
        os.unlink(f.name)
    return 'accepted' if v.returncode == 0 else (v.stdout + v.stderr).strip()

if __name__ == '__main__':
    fc_solve, freecell, out = sys.argv[1:4]
    with open(out, 'a') as f:
        for d in map(int, sys.argv[4:]):
            try:
                o = solve(fc_solve, freecell, d)
            except Exception as e:  # report and continue; nothing here is trusted
                o = {'result': 'error', 'error': repr(e)}
            f.write(json.dumps({'deal': d, 'exit': 0 if o['result'] == 'winnable' else 3, 'output': o}) + '\n')
            f.flush()
            print(d, o['result'], o.get('moveCount', o.get('reason', o.get('error'))), file=sys.stderr, flush=True)
