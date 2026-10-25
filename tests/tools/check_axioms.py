"""Compare `#print axioms` output for the per-deal results with the expected sets.

Usage: lake env lean tests/ExamplesAxioms.lean | python3 tests/tools/check_axioms.py
Expected:
- ms32000_winnable_iff: the standard axioms plus exactly 33 native_decide axioms,
  one per chunk01..chunk32 and one for deal11982_unwinnable;
- Examples.Deals theorems: the standard axioms plus their own native_decide axiom;
- kernel_deal*: the standard axioms only (no native_decide).
"""
import re, sys

STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
text = sys.stdin.read()
reports = {m.group(1): {a.strip() for a in m.group(2).split(',') if a.strip()}
           for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, re.S)}
errors = []

def expect(name, allowed_extra, exact_extra=None):
    if name not in reports:
        errors.append(f'{name}: no axiom report'); return
    ax = reports[name]
    extra = ax - STANDARD
    if exact_extra is not None and extra != exact_extra:
        errors.append(f'{name}: extra axioms {sorted(extra ^ exact_extra)} differ from expected')
    elif exact_extra is None and not allowed_extra(extra):
        errors.append(f'{name}: unexpected axioms {sorted(extra)}')

M = 'FreeCell.Examples.Ms32000.'
want = {f'{M}chunk{k:02d}._native.native_decide.ax_1_1' for k in range(1, 33)}
want.add(f'{M}deal11982_unwinnable._native.native_decide.ax_1_1')
expect(f'{M}ms32000_winnable_iff', None, want)
for t in ['deal11982_unwinnable', 'deal1_winnable', 'deal1941_winnable']:
    name = f'FreeCell.Examples.{t}'
    expect(name, None, {f'{name}._native.native_decide.ax_1_1'})
kernel = [n for n in reports if n.startswith('FreeCell.Examples.Ms32000Kernel.')]
for n in kernel:
    expect(n, lambda extra: not extra)
if len(kernel) < 15:
    errors.append(f'only {len(kernel)} kernel-checked deals reported, expected 15')
if errors:
    print('\n'.join(errors)); sys.exit(1)
print(f'axioms as expected: ms32000_winnable_iff has the 3 standard + 33 native_decide axioms; '
      f'{len(kernel)} kernel-checked deals use only the standard axioms')
