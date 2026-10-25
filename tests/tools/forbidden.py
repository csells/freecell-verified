"""Flag Lean constructs that could weaken or bypass the proofs.

Comments and string literals are removed first, so prose may mention any of these
words; in code each pattern matches anywhere on a line, whatever precedes it.

Usage: python3 tests/tools/forbidden.py [--allow-native] FILE_OR_DIR ...
Prints each hit as FILE:LINE: TEXT and exits 1 if there are any.
--allow-native permits `native_decide` (and only that), for Examples/.
"""
import os, re, sys

PATTERNS = [
    r'\bsorry\b', r'\badmit\b', r'\baxiom\b', r'\bpartial\b', r'\bunsafe\b', r'\bopaque\b',
    r'\bimplemented_by\b', r'\bextern\b', r'\bexport\b', r'\bcsimp\b', r'\bnative_decide\b',
    r'\bdecide\s*\+\s*native\b', r'\bofReduceBool\b', r'\bofReduceNat\b', r'\breduceBool\b',
    r'\bskipKernelTC\b', r'\bdebug\.\w+', r'\battribute\s*\[', r'\bmacro(_rules)?\b',
    r'\belab(_rules)?\b', r'\bsyntax\b', r'\bnotation\b', r'\binfix[lr]?\b', r'\bprefix\b',
    r'\bpostfix\b', r'\bset_option\b', r'\binitialize\b', r'\bbuiltin_initialize\b',
    r'\brun_cmd\b', r'\brun_tac\b', r'#eval\b', r'\bLean\.Elab\b', r'\bLean\.Meta\b',
]
NATIVE = r'\bnative_decide\b'

def strip(text):
    """Blank out comments (nested /- -/ and --) and string/char literals, keeping newlines."""
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        c = text[i]
        if depth:
            if text.startswith('/-', i): depth += 1; i += 2; continue
            if text.startswith('-/', i): depth -= 1; i += 2; continue
            out.append('\n' if c == '\n' else ' '); i += 1; continue
        if text.startswith('/-', i): depth = 1; i += 2; out.append('  '); continue
        if text.startswith('--', i):
            j = text.find('\n', i); j = n if j < 0 else j
            out.append(' ' * (j - i)); i = j; continue
        if c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            out.append('"' + ''.join('\n' if ch == '\n' else ' ' for ch in text[i + 1:j]) + '"')
            i = j + 1; continue
        if c == "'" and i + 2 < n and (text[i + 2] == "'" or (text[i + 1] == '\\' and text.find("'", i + 2) - i <= 8)):
            j = text.find("'", i + 2) if text[i + 1] == '\\' else i + 2
            out.append("'" + ' ' * (j - i - 1) + "'"); i = j + 1; continue
        out.append(c); i += 1
    return ''.join(out)

def files(paths):
    for p in paths:
        if os.path.isdir(p):
            for root, _, names in os.walk(p):
                for f in sorted(names):
                    if f.endswith('.lean'): yield os.path.join(root, f)
        else:
            yield p

def main(argv):
    allow_native = '--allow-native' in argv
    paths = [a for a in argv if a != '--allow-native']
    pats = [re.compile(p) for p in PATTERNS if not (allow_native and p == NATIVE)]
    hits = 0
    for f in files(paths):
        raw = open(f, encoding='utf-8').read()
        for ln, (code, orig) in enumerate(zip(strip(raw).split('\n'), raw.split('\n')), 1):
            if any(p.search(code) for p in pats):
                print(f'{f}:{ln}: {orig.strip()}'); hits += 1
    return 1 if hits else 0

if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
