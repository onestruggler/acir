"""The pair lemmas of macro.py up to the symmetries of the 4-cube (wire
permutations and X on wires, which act on coloured gates).

python pairs.py            prints the orbits
"""
import itertools

import macro as M


def act(sym, g):
    perm, mask = sym
    t, cs = M.GATES[g]
    return M.GID[(perm[t], tuple(sorted((perm[c], v ^ (mask >> perm[c] & 1)) for c, v in cs)))]


SYMS = [(p, m) for p in itertools.permutations(range(4)) for m in range(16)]


def orbit_key(g, h):
    """Canonical representative of the unordered pair lemma {g, h}."""
    best = None
    for s in SYMS:
        a, b = act(s, g), act(s, h)
        for x in ((a, b), (b, a)):
            if best is None or x < best:
                best = x
    return best


def describe(g, h):
    k = M.PAIR[(g, h)]
    (t, cs), (u, ds) = M.GATES[g], M.GATES[h]
    dc, dd = dict(cs), dict(ds)
    opp = any(dc[w] != dd[w] for w in set(dc) & set(dd))
    if t == u:
        rel = 'same target'
    elif t in dd and u in dc:
        rel = 'mutual'
    elif t in dd or u in dc:
        rel = 'target is control'
    else:
        rel = 'disjoint targets, shared controls'
    return '%d+%d controls, %s%s; (g h)^2 = %s' % (
        len(cs), len(ds), rel, ', opposite colours on a shared control' if opp else '',
        'id' if k == -1 else M.gname(k))


ORBITS = {}
for (g, h) in M.PAIR:
    ORBITS.setdefault(orbit_key(g, h), []).append((g, h))

if __name__ == '__main__':
    for key in sorted(ORBITS):
        g, h = key
        print('%-10s %-10s  %s  (x%d)' % (M.gname(g), M.gname(h), describe(g, h), len(ORBITS[key])))
    print(len(ORBITS), 'orbits of pair lemmas')
