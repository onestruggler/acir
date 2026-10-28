"""Python model of Sec8/D/SymEngine.lean.

Letters: ('s', kind, j) with kind in H Z C K S (CZ on j,j+1; CH with H on j,
control j+1; swap j,j+1); ('g', Kd, tg, cs, b) with Kd in box zx xz hg, tg a
tuple, cs a tuple of (wire, bool), b the bulk flag.
"""
import sys
sys.path.insert(0, '.')
from mc import *
import numpy as np

def S(kind, j): return ('s', kind, j)
def G(Kd, tg, cs, b): return ('g', Kd, tuple(tg), tuple(cs), b)

def ctl(K, cs, b):
    d = dict(cs)
    return lambda j: d.get(j) if j < K else (True if b else None)

def small(N, kind, j):
    if kind == 'H': return [('H', j)]
    if kind == 'Z': return [('Z', j)]
    if kind == 'C': return [('CZ', j)]
    if kind == 'K': return [('CH', j)]
    if kind == 'S': return swAt(N, j)
    raise ValueError(kind)

def lo(x): return x[2]
def wd(x): return 1 if x[1] in 'HZ' else 2

def circ(K, N, x):
    if x[0] == 's': return small(N, x[1], x[2])
    _, Kd, tg, cs, b = x
    return mc(N, Kd, list(tg), ctl(K, cs, b))

def wc(K, N, w):
    out = []
    for x in w: out += circ(K, N, x)
    return out

def ok(K, x):
    if x[0] == 's': return lo(x) + wd(x) <= K
    _, Kd, tg, cs, b = x
    ar = 2 if Kd == 'hg' else 1
    return len(set(tg)) == len(tg) and all(t < K for t in tg) and len(tg) == ar

def on(K, x):
    return circ(K, K, x)

def off(K, x):
    if x[0] == 'g' and x[4]: return []
    return circ(K, K, x)

def avoids(q, x):
    if x[0] == 's': return lo(x) + wd(x) <= q or q < lo(x)
    _, Kd, tg, cs, b = x
    return q not in tg and all(p != q for p, _ in cs)

def dropW(q, j): return j if j < q else j - 1

def drop(q, x):
    if x[0] == 's': return ('s', x[1], x[2] - 1) if q < x[2] else x
    _, Kd, tg, cs, b = x
    return ('g', Kd, tuple(dropW(q, t) for t in tg), tuple((dropW(q, p), v) for p, v in cs), b)

def eqm(N, a, b): return np.allclose(mat(N, a), mat(N, b))

def semOK(k, q, a, b):
    """k + 1 local wires; window avoids q; checked on k wires."""
    if q > k: return False
    if not all(ok(k + 1, x) and avoids(q, x) for x in a + b): return False
    da = [drop(q, x) for x in a]; db = [drop(q, x) for x in b]
    if not all(ok(k, x) for x in da + db): return False
    on_a = [g for x in da for g in on(k, x)]; on_b = [g for x in db for g in on(k, x)]
    of_a = [g for x in da for g in off(k, x)]; of_b = [g for x in db for g in off(k, x)]
    return eqm(k, on_a, on_b) and eqm(k, of_a, of_b)

def disj(x, y):
    return lo(x) + wd(x) <= lo(y) or lo(y) + wd(y) <= lo(x)

def apply(k, T, cur, st):
    if st[0] == 'rw':
        _, i, e, d = st
        l, r = T[e] if not d else (T[e][1], T[e][0])
        if tuple(cur[i:i + len(l)]) != tuple(l): return None
        return cur[:i] + list(r) + cur[i + len(l):]
    if st[0] == 'sw':
        i = st[1]
        x, y = cur[i], cur[i + 1]
        if x[0] == 's' and y[0] == 's' and disj(x, y): return cur[:i] + [y, x] + cur[i + 2:]
        return None
    if st[0] == 'sem':
        _, i, ln, r, q = st
        win = cur[i:i + ln]
        if len(win) != ln or not semOK(k, q, win, list(r)): return None
        return cur[:i] + list(r) + cur[i + ln:]

def run(k, T, w, steps, verbose=False):
    cur = list(w)
    for n, st in enumerate(steps):
        nxt = apply(k, T, cur, st)
        if nxt is None:
            print('FAILED at step', n, st); print('  cur =', cur); return None
        if verbose: print(n, st[0], nxt)
        cur = nxt
    return cur

def check_eq(K, l, r, Ns=None):
    """numerically: l = r at widths K .. K+2"""
    Ns = Ns or range(K, K + 3)
    return [(N, eqm(N, wc(K, N, l), wc(K, N, r))) for N in Ns]

def sem_any(k, a, b):
    """the qs for which a window replacement a -> b is a valid sem step"""
    return [q for q in range(k + 1) if semOK(k, q, a, b)]
