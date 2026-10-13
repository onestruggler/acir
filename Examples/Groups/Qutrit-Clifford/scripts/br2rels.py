"""The two-qutrit box relations (BoxRelations₂ of Tables.agda), as pairs
of words over n h s H S c, in operator order."""
import os
ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import re
from pauli_act import ev, defs as NFdefs

CH = {('H', 0): 'h', ('S', 0): 's', ('H', 1): 'H', ('S', 1): 'S', ('CZ', 0): 'c', ('nu',): 'n'}
def word(lst):
    return ''.join(CH[t] for t in lst)
def box(k, ix):
    return word(ev(NFdefs['%sl %s%s' % (k, k, ''.join('₀₁₂'[i] for i in ix))]))
SUB = '₀₁₂'
def idx(name):
    return tuple(SUB.index(c) for c in name[1:])
UPPER = str.maketrans('hs', 'HS')
X = word(ev(NFdefs['Xˡ'])); Z = word(ev(NFdefs['Zˡ']))
W0 = {'iS': 's', 'iX': X, 'iZ': Z, 'iν': 'n'}
HS = {'gH': 'h', 'gS': 's'}
SCO = {'scC': 'c', 'scH': 'h', 'scS': 's', 'scν': 'n'}
O2 = {'oh₁': 'H', 'os₁': 'S', 'oS₀': 's', 'oZ₀': Z, 'oν': 'n'}
def post(t):
    t = t.strip()
    if t.startswith('(pin '): return W0[t[5:-1]].translate(UPPER)
    return {'pH': 'h', 'pS': 's', 'pstr': 'c', 'pν': 'n'}[t]
def in1(t):
    t = t.strip()
    if t.startswith('(w0 '): return W0[t[4:-1]]
    if t.startswith('(w1 '): return HS[t[4:-1]].translate(UPPER)
    raise ValueError(t)

def toks(lst):
    lst = lst.strip()
    if lst == '[]': return []
    parts = []; depth = 0; cur = ''
    for ch in lst:
        if ch == '(': depth += 1
        if ch == ')': depth -= 1
        if ch == '∷' and depth == 0:
            parts.append(cur.strip()); cur = ''
        else:
            cur += ch
    parts.append(cur.strip())
    assert parts[-1] == '[]', lst
    return parts[:-1]

T = open(ROOT + '/Tables.agda', encoding='utf-8').read()
A = lambda a: box('A', idx(a)); B = lambda b: box('B', idx(b))
C = lambda c: box('C', idx(c)); D = lambda d: box('D', idx(d))

REL = []    # (field, args, lhs, rhs)
for m in re.finditer(r'^ruleAup (A\S+) = inj₁ \((A\S+) , (.*)\)$', T, re.M):
    a, a2, lst = m.groups()
    REL.append(('ruleAup', (a,), A(a).translate(UPPER) + 'c', ''.join(post(t) for t in toks(lst)) + A(a2).translate(UPPER)))
for m in re.finditer(r'^ruleAup (A\S+) = inj₂ \((A\S+) , (B\S+) , (.*)\)$', T, re.M):
    a, a2, b2, lst = m.groups()
    REL.append(('ruleAup', (a,), A(a).translate(UPPER) + 'c', ''.join(post(t) for t in toks(lst)) + B(b2) + A(a2)))
for m in re.finditer(r'^ruleAB (A\S+) (B\S+) = inj₁ \((A\S+) , (B\S+) , (.*)\)$', T, re.M):
    a, b, a2, b2, lst = m.groups()
    REL.append(('ruleAB', (a, b), B(b) + A(a) + 'c', ''.join(post(t) for t in toks(lst)) + B(b2) + A(a2)))
for m in re.finditer(r'^ruleAB (A\S+) (B\S+) = inj₂ \((A\S+) , (.*)\)$', T, re.M):
    a, b, a2, lst = m.groups()
    REL.append(('ruleAB', (a, b), B(b) + A(a) + 'c', ''.join(post(t) for t in toks(lst)) + A(a2).translate(UPPER)))
for m in re.finditer(r'^ruleB (B\S+) (\(w\S+ \S+\)) = (B\S+) , (.*)$', T, re.M):
    b, g, b2, lst = m.groups()
    REL.append(('ruleB', (b, g), B(b) + in1(g), ''.join(post(t) for t in toks(lst)) + B(b2)))
for m in re.finditer(r'^ruleSC (C\S+) = (C\S+) , (.*)$', T, re.M):
    c, c2, lst = m.groups()
    REL.append(('ruleSC', (c,), C(c).translate(UPPER) + 'c', ''.join(SCO[t.strip()] for t in toks(lst)) + C(c2).translate(UPPER)))
for m in re.finditer(r'^ruleD (D\S+) (g\S) = (D\S+) , (.*)$', T, re.M):
    d, h, d2, lst = m.groups()
    REL.append(('ruleD', (d, h), D(d) + HS[h], ''.join(O2[t.strip()] for t in toks(lst)) + D(d2)))
for m in re.finditer(r'^ruleCD (D\S+) = (D\S+) , (.*)$', T, re.M):
    d, d2, lst = m.groups()
    REL.append(('ruleCD', (d,), D(d) + 'c', ''.join(O2[t.strip()] for t in toks(lst)) + D(d2)))
for a in range(3):
    for b in range(3):
        d = 'D' + SUB[a] + SUB[b]
        REL.append(('ruleS1D', (d,), D(d) + 'S', 's' + D(d)))
        REL.append(('ruleZ1D', (d,), D(d) + Z.translate(UPPER), Z + D(d)))
REL.append(('id₂', (), D('D₀₁') + B('B₀₀'), ''))

if __name__ == '__main__':
    import coset2 as C2
    from collections import Counter
    print(Counter(f for f, *_ in REL))
    bad = [r for r in REL if C2.opmat(r[2]) != C2.opmat(r[3])]
    print('semantically wrong:', len(bad))
