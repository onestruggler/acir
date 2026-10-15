"""Controlled HH with one borrowed wire, as two conjugated Toffolis.

On the block of wires a=0, b=1, beta=2 (three wires), K = HH0 (x) I is a
product of four reflections in orthogonal roots.  Split them into two
pairs; each pair is s_r s_r' = V (CX0 (x) I) V^-1 for a three-wire
circuit V (CX0 swaps |010>,|011> and |110>,|111>: the roots e2-e3,
e6-e7).  Then controlled-K = V ctrl(CX0) V^-1 . V' ctrl(CX0) V'^-1."""
import sys, itertools
sys.path.insert(0, '..')
from e8 import root_orbit, ACT, dot
roots = list(root_orbit())
def act(word, v):
    for g in reversed(word): v = ACT[g](v)
    return v
neg = lambda r: tuple(-a for a in r)
minus = [r for r in roots if act(['HH0'], r) == neg(r)]
pos = []
for r in minus:
    if neg(r) not in pos: pos.append(r)
print('roots of K (x) I, up to sign:', pos)
assert len(pos) == 4 and all(dot(a, b) == 0 for a, b in itertools.combinations(pos, 2))
E = [tuple(2 if j == i else 0 for j in range(8)) for i in range(8)]
r23 = tuple(a - b for a, b in zip(E[2], E[3])); r67 = tuple(a - b for a, b in zip(E[6], E[7]))
LET = ['X0', 'X1', 'X2', 'CX0', 'CX1', 'CCX0', 'HH0', 'HH1']
def canon(r): return r if next(a for a in r if a) > 0 else neg(r)
def find_V(p, q):
    """BFS on words V (prepending letters) for the pair of root lines."""
    target = {canon(p), canon(q)}
    start = (canon(r23), canon(r67))
    seen = {start: ()}
    fr = [start]
    while fr:
        nw = []
        for st in fr:
            if set(st) == target:
                return seen[st]
            for g in LET:
                img = (canon(ACT[g](st[0])), canon(ACT[g](st[1])))
                if img not in seen:
                    seen[img] = (g,) + seen[st]; nw.append(img)
        fr = nw
    return None
best = None
for pairing in [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]:
    (i, j), (k, l) = pairing
    V1 = find_V(pos[i], pos[j]); V2 = find_V(pos[k], pos[l])
    tot = len(V1) + len(V2)
    print(pairing, ' '.join(V1), '|', ' '.join(V2), 'total', tot)
    if best is None or tot < best[0]: best = (tot, V1, V2)
print('best', best)
