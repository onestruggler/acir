"""Search for a simple system of E8 whose reflections have short circuits."""
import random, itertools, sys
from e8 import *

W = root_orbit()
def circ(r):
    w = W[r]
    return w + ['CCX0'] + list(reversed(w))
def cost(r):
    c = circ(r)
    return len(c), sum(1 for g in c if g.startswith('HH'))

def simple_system(f):
    pos = [r for r in W if dot(r, f) > 0]
    pset = set(pos)
    simple = []
    for r in pos:
        dec = False
        for s in pos:
            t = tuple(a - b for a, b in zip(r, s))
            if t in pset:
                dec = True; break
        if not dec:
            simple.append(r)
    return simple

def coxeter(simple):
    m = [[1]*8 for _ in range(8)]
    for i, j in itertools.combinations(range(8), 2):
        d = dot(simple[i], simple[j])
        m[i][j] = m[j][i] = {0: 2, -4: 3, 4: 3}[d]
    return m

best = []
rnd = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
seen = set()
for trial in range(20000):
    f = tuple(rnd.gauss(0, 1) for _ in range(8))
    S = simple_system(f)
    assert len(S) == 8
    key = frozenset(map(canon, S))
    if key in seen: continue
    seen.add(key)
    tot = sum(cost(r)[0] for r in S)
    hhc = sum(1 for r in S if cost(r)[1] > 0)
    best.append((hhc, tot, S))
best.sort(key=lambda t: (t[0], t[1]))
print('distinct systems tried', len(seen))
for hhc, tot, S in best[:5]:
    print('HH-reflections', hhc, 'total length', tot)
    for r in S:
        print('   ', r, ' '.join(circ(r)))
    M = coxeter(S)
    print('    coxeter rows', [''.join(str(x) for x in row) for row in M])
