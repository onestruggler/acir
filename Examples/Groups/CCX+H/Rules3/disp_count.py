import itertools
from table import T1, T2, holds

def count(con, order):
    vs, args = order, con[2]
    n = 0
    def rec(vals):
        nonlocal n
        j = len(vals)
        if j == len(vs):
            n += 1; return
        for x in range(8):
            v = dict(zip(vs, vals + [x]))
            bad = any(all(t in v for t in a[1:] if isinstance(t, str)) and vs[j] in a[1:] and not holds(a, v) for a in args)
            if bad: n += 1
            else: rec(vals + [x])
    rec([])
    return n

for con in T1 + T2:
    vs = con[1].split()
    base = count(con, vs)
    best = base; bo = vs
    if len(vs) <= 6:
        for p in itertools.permutations(vs):
            c = count(con, list(p))
            if c < best: best, bo = c, list(p)
    print(con[0], len(vs), base, best, ' '.join(bo))
