"""Subcase 1.2.2.3 with u_e odd: check the paper's two diagrams."""
import random, sys
from alg import *

def mone(x):
    return ('n', x)

def run(trials, seed):
    rng = random.Random(seed)
    stats = {'case0': 0, 'case8': 0}
    fails = []
    for _ in range(trials):
        n = rng.choice([8, 9, 10, 11, 12])
        s = random_state(n, rng.randrange(4, 30), rng)
        L = level(s)
        if L[0] == 0 or L[1] == 0:
            continue
        u, k = wint(s)
        odd = [r for r in range(n) if u[r] % 2]
        a, b, c, d = odd[:4]
        e = d + 1
        if e >= n or u[e] % 2 == 0:
            continue
        g = ('x', d, e)
        if not level(gen_apply(g, s)) <= L:
            fails.append(('raises', L))
            continue
        f, gg, h = odd[5:8]
        assert odd[4] == e
        ub = [u[x] for x in odd[:8]]
        nrm = sum(x * x for x in ub) % 16
        assert nrm in (0, 8)
        if nrm == 0:
            W = [mone(a), mone(e), ('x', a, e)]
            stats['case0'] += 1
        else:
            W = [mone(a), mone(h), ('x', a, h)]
            stats['case8'] += 1
        T = [('k', e, f, gg, h), ('k', a, b, c, d)] + W
        Tinv = list(reversed(T))
        t = nxt(s)
        P = Tinv + [g] + T + syll(t)
        ok, bad, _ = check_square(s, g, 2, P)
        if not ok or bad:
            fails.append((n, L, nrm, ok, bad, [u[x] % 16 for x in odd[:8]]))
    return stats, fails

if __name__ == '__main__':
    stats, fails = run(int(sys.argv[1]), int(sys.argv[2]))
    print(stats, len(fails))
    for f in fails[:10]:
        print(f)
