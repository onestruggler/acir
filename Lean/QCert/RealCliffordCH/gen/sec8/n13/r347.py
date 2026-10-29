"""Numerical checks for N13/RotDec and N13/E347 ((347)-(352)).

Run with Windows python (numpy): python r347.py [dec]
* dec: the decomposition of a coloured rotation, any t, b, h, N = 3..5 (slow).
* default: the piece pairs of the chosen decompositions commute.
"""
import sys, itertools
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import numpy as np
from mc import mc_sem, Hm

def S(N, K, tg, d):
    return mc_sem(N, K, tg, lambda j: d.get(j))

def comm(A, B): return np.allclose(A @ B, B @ A)

def pieces(N, t, b, h, z):
    hgc = {w: z[w] for w in z if w not in (h, t)}
    bc = {w: z[w] for w in z if w not in (b, t)}; bc[t] = True
    return [('hg', S(N, 'hg', [h, t], hgc)), ('box', S(N, 'box', [b], bc))]

def rot(N, a, t, z): return S(N, 'xz' if a else 'zx', [t], z)



bad = {}
def note(k): bad[k] = bad.get(k, 0) + 1

for N in [3, 4, 5]:
    W = list(range(2, N))
    for xs in itertools.product([False, True], repeat=len(W)):
        for ys in itertools.product([False, True], repeat=len(W)):
            x = dict(zip(W, xs)); y = dict(zip(W, ys))
            if x == y: continue
            j = min(w for w in W if x[w] != y[w])
            alt = [w for w in W if w != j]
            for c1, c2 in itertools.product([False, True], repeat=2):
                # (347): box[0](1:c1, x) vs R[1](0:c2, y); (t=1, h=0, b=2)
                O = S(N, 'box', [0], {1: c1, **x})
                z = {0: c2, **y}
                for nm, P in pieces(N, 1, 2, 0, z):
                    if not comm(O, P): note(('347', N, nm))
                # (348): hg[0,1](x) vs R[0](1:c1, y); (t=0, b=1, h != j)
                O = S(N, 'hg', [0, 1], x)
                z = {1: c1, **y}
                if alt:
                    for nm, P in pieces(N, 0, 1, alt[0], z):
                        if not comm(O, P): note(('348', N, nm))
                else: note(('348', N, 'no-h'))
                # (349): hg[0,1](x) vs R[1](0:c1, y); (t=1, h=0, b != j)
                z = {0: c1, **y}
                if alt:
                    for nm, P in pieces(N, 1, alt[0], 0, z):
                        if not comm(O, P): note(('349', N, nm))
                else: note(('349', N, 'no-b'))
                # (352): R[0](1:c1, x) vs R[1](0:c2, y); (h1=1, b1=b), (h2=0, b2=b), b != j
                if alt:
                    b = alt[0]
                    p1 = pieces(N, 0, b, 1, {1: c1, **x})
                    p2 = pieces(N, 1, b, 0, {0: c2, **y})
                    for n1, P1 in p1:
                        for n2, P2 in p2:
                            if not comm(P1, P2): note(('352', N, n1, n2))
                else: note(('352', N, 'no-b'))
            # (350): N >= 4: hg[0,1](2:c1, x on >=3) vs R[2](1:c2, 0:c3, y on >=3), (t=2,b=0,h=1)
    if N >= 4:
        W3 = list(range(3, N))
        for xs in itertools.product([False, True], repeat=len(W3)):
            for ys in itertools.product([False, True], repeat=len(W3)):
                x = dict(zip(W3, xs)); y = dict(zip(W3, ys))
                if x == y: continue
                for c1, c2, c3 in itertools.product([False, True], repeat=3):
                    O = S(N, 'hg', [0, 1], {2: c1, **x})
                    for nm, P in pieces(N, 2, 0, 1, {1: c2, 0: c3, **y}):
                        if not comm(O, P): note(('350', N, nm))
    # (351): R[0](x) vs R[0](y), x != y on 1..N-1, same (b, h) avoiding j
    W1 = list(range(1, N))
    for xs in itertools.product([False, True], repeat=len(W1)):
        for ys in itertools.product([False, True], repeat=len(W1)):
            x = dict(zip(W1, xs)); y = dict(zip(W1, ys))
            if x == y: continue
            j = min(w for w in W1 if x[w] != y[w])
            alt = [w for w in W1 if w != j]
            if len(alt) < 2: note(('351', N, 'few')); continue
            b, h = alt[0], alt[1]
            for n1, P1 in pieces(N, 0, b, h, x):
                for n2, P2 in pieces(N, 0, b, h, y):
                    if not comm(P1, P2): note(('351', N, n1, n2))
print(bad)

if len(sys.argv) > 1 and sys.argv[1] == 'dec':
    from mc import mat, mc, drawn
    def rotc(N, a, t, z): return mc(N, 'xz' if a else 'zx', [t], lambda j: z.get(j))
    def piecesc(N, t, b, h, z):
        hgc = {w: z[w] for w in z if w not in (h, t)}
        bc = {w: z[w] for w in z if w not in (b, t)}; bc[t] = True
        return mc(N, 'hg', [h, t], lambda j: hgc.get(j)), mc(N, 'box', [b], lambda j: bc.get(j))
    badd = 0
    for N in [3, 4, 5]:
        for a in [0, 1]:
            for t in range(N):
                others = [w for w in range(N) if w != t]
                for b, h in itertools.permutations(others, 2):
                    for bits in itertools.product([False, True], repeat=len(others)):
                        z = dict(zip(others, bits))
                        HG, B = piecesc(N, t, b, h, z)
                        rhs = drawn(B, HG, B, HG) if a else drawn(HG, B, HG, B)
                        if not np.allclose(mat(N, rotc(N, a, t, z)), mat(N, rhs)): badd += 1
    print('decomposition: bad', badd)
