"""Convert an independent Python witness (a list of states) into a winnable certificate.

Untrusted glue: the Lean checker decides whether the resulting move list is legal and wins.
Witness states are (columns bottom-to-top, sorted cells, foundation heights) with card
code c = 4*(rank-1) + suit, suits CDHS.
"""
import json, sys

name = lambda c: 'A23456789TJQK'[c // 4] + 'CDHS'[c % 4]

def compact(st):
    cs, fs, hs = st
    return '.'.join(map(str, hs)) + '|' + ' '.join(map(name, fs)) + '|' + \
        '|'.join(' '.join(map(name, col)) for col in cs)

def move(a, b):
    (ca, fa, ha), (cb, fb, hb) = a, b
    src = dst = None
    for i in range(8):
        if len(cb[i]) < len(ca[i]): src = f'c{i + 1}'; card = ca[i][-1]
        if len(cb[i]) > len(ca[i]): dst = f'c{i + 1}'
    for c in fa:
        if c not in fb: src = f'f:{name(c)}'; card = c
    if len(fb) > len(fa) or (src and src.startswith('c') and len(fb) == len(fa) and fb != fa): dst = 'f'
    if sum(hb) > sum(ha): dst = 'h'
    if src is None or dst is None: raise SystemExit(f'cannot interpret transition {a} -> {b}')
    return f'{src} {dst}'

d = json.load(open(sys.argv[1]))
path = d['path']
moves = [move(a, b) for a, b in zip(path, path[1:])]
print('freecell-verified certificate v1')
print('rules: standard-freecell/single-card/4-cells/v1')
print('start: ' + compact(path[0]))
print(f'winnable: {len(moves)}')
print('\n'.join(moves))
