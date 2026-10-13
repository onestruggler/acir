"""Read the box letter lists of NormalForm.agda and compare with boxes.py."""
import os
ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import re
from qt import eq
from boxes import A, B, C, D, E, F
LETTER = {'𝕟': ('nu',), 'h₀': ('H', 0), 'h₁': ('H', 1), 's₀': ('S', 0), 's₁': ('S', 1), 'c₀': ('CZ', 0)}
src = open(ROOT + '/NormalForm.agda', encoding='utf-8').read()
defs = {}
for line in src.splitlines():
    m = re.match(r'^(\w+ˡ|\w+ \w+)\s+=\s+(.*)$', line)
    if m:
        defs[m.group(1)] = m.group(2)
def ev(expr):
    out = []
    for part in expr.split('++'):
        part = part.strip()
        if part.startswith('map _↥ (') and part.endswith(')'):
            inner = ev(part[len('map _↥ ('):-1])
            out += [t if t[0] == 'nu' else (t[0], t[1] + 1) for t in inner]
            continue
        toks = [t.strip() for t in part.split('∷')]
        for t in toks[:-1]:
            out.append(LETTER[t])
        t = toks[-1]
        if t == '[]': pass
        elif t in LETTER: out.append(LETTER[t])
        elif t.startswith('map _↥ ('): out += ev(t)
        elif t.startswith('(') and t.endswith(')'): out += ev(t[1:-1])
        else: out += ev(defs[t])
    return out
sub = '₀₁₂'
ok = True
for key, val in defs.items():
    m = re.match(r'^([ABCDEF])l ([ABCDEF])(\S+)$', key)
    if not m: continue
    k, ix = m.group(1), [sub.index(c) for c in m.group(3)]
    n = 2 if k in 'BD' else 1
    py = {'A': A, 'B': B, 'C': C, 'D': D, 'E': E, 'F': F}[k](*ix)
    agda = list(reversed(ev(val)))   # operator order -> time order
    if not eq(agda, py, n):
        print('MISMATCH', key); ok = False
print('all boxes agree' if ok else 'FAIL')
