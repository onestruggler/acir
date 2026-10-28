"""Instances of the relations of Table 1 on local indices 0..m-1, in the
conventions of Lean's QCert.LiRossSelinger.Checker (`sides`)."""
from itertools import combinations, permutations

def N(a): return ('n', a)
def X(a, b): return ('x', a, b)
def K(a, b, c, d): return ('k', a, b, c, d)

def sides(fam, ps):
    """Return (lhs, rhs) as tuples, or None if not well-formed."""
    p = ps
    def inc(*xs): return all(xs[i] < xs[i + 1] for i in range(len(xs) - 1))
    def nd(*xs): return len(set(xs)) == len(xs)
    if fam == 'r1a':
        a, b = p; return ((X(a, b), X(a, b)), ()) if a < b else None
    if fam == 'r1b':
        a, = p; return ((N(a), N(a)), ())
    if fam == 'r1c':
        if not inc(*p): return None
        return ((K(*p), K(*p)), ())
    if fam == 'r2a':
        a, b, c, d = p
        if not (a < b and c < d and nd(a, b, c, d)): return None
        return ((X(a, b), X(c, d)), (X(c, d), X(a, b)))
    if fam == 'r2b':
        a, b, c = p
        if not (a < b and nd(a, b, c)): return None
        return ((X(a, b), N(c)), (N(c), X(a, b)))
    if fam == 'r2c':
        a, b, c, d, e, f = p
        if not (a < b and inc(c, d, e, f) and nd(*p)): return None
        return ((X(a, b), K(c, d, e, f)), (K(c, d, e, f), X(a, b)))
    if fam == 'r2d':
        a, b = p
        if a == b: return None
        return ((N(a), N(b)), (N(b), N(a)))
    if fam == 'r2e':
        a, b, c, d, e = p
        if not (inc(b, c, d, e) and nd(*p)): return None
        return ((N(a), K(b, c, d, e)), (K(b, c, d, e), N(a)))
    if fam == 'r2f':
        a, b, c, d, e, f, g, i = p
        if not (inc(a, b, c, d) and inc(e, f, g, i) and nd(*p)): return None
        return ((K(a, b, c, d), K(e, f, g, i)), (K(e, f, g, i), K(a, b, c, d)))
    if fam == 'r3a':
        a, a1, b = p
        if not inc(a, a1, b): return None
        return ((X(a, a1), X(a, b)), (X(a1, b), X(a, a1)))
    if fam == 'r3b':
        a, b, b1 = p
        if not inc(a, b, b1): return None
        return ((X(b, b1), X(a, b)), (X(a, b1), X(b, b1)))
    if fam == 'r3c':
        a, b = p
        if not a < b: return None
        return ((X(a, b), N(b)), (N(a), X(a, b)))
    if fam == 'r3d':
        a, a1, b, c, d = p
        if not inc(*p): return None
        return ((X(a, a1), K(a, b, c, d)), (K(a1, b, c, d), X(a, a1)))
    if fam == 'r3e':
        a, b, b1, c, d = p
        if not inc(*p): return None
        return ((X(b, b1), K(a, b, c, d)), (K(a, b1, c, d), X(b, b1)))
    if fam == 'r3f':
        a, b, c, c1, d = p
        if not inc(*p): return None
        return ((X(c, c1), K(a, b, c, d)), (K(a, b, c1, d), X(c, c1)))
    if fam == 'r3g':
        a, b, c, d, d1 = p
        if not inc(*p): return None
        return ((X(d, d1), K(a, b, c, d)), (K(a, b, c, d1), X(d, d1)))
    if fam == 'r4a':
        a, b, c, d = p
        if not inc(*p): return None
        return ((X(a, b), K(a, b, c, d)), (K(a, b, c, d), X(b, d), N(b), N(d)))
    if fam == 'r4b':
        a, b, c, d = p
        if not inc(*p): return None
        k = K(a, b, c, d)
        return ((X(b, c), k), (N(a), k, N(a), k, N(a)))
    if fam == 'r4c':
        a, b, c, d = p
        if not inc(*p): return None
        return ((X(c, d), K(a, b, c, d)), (K(a, b, c, d), X(b, d)))
    if fam == 'r5a':
        a, b, c, d, e, f = p
        if not inc(*p): return None
        return ((K(a, b, c, d), K(b, d, e, f)), (K(c, d, e, f), K(a, b, c, e)))
    if fam == 'r6a':
        a, b, c, d, e, f, g, h = p
        if not inc(*p): return None
        core = (K(e, f, g, h), K(a, b, c, d), X(d, e), K(a, b, c, d), K(e, f, g, h))
        return ((N(a), N(e), X(a, e)) + core + (X(a, e), N(a), N(e)), core)
    raise ValueError(fam)

ARITY = {'r1a': 2, 'r1b': 1, 'r1c': 4, 'r2a': 4, 'r2b': 3, 'r2c': 6, 'r2d': 2, 'r2e': 5,
         'r2f': 8, 'r3a': 3, 'r3b': 3, 'r3c': 2, 'r3d': 5, 'r3e': 5, 'r3f': 5, 'r3g': 5,
         'r4a': 4, 'r4b': 4, 'r4c': 4, 'r5a': 6, 'r6a': 8}

def instances(m, fams=None):
    """All (fam, ps, lhs, rhs) on Fin m."""
    out = []
    for fam, k in ARITY.items():
        if fams is not None and fam not in fams:
            continue
        if k > m:
            continue
        # sorted families: use combinations; others: permutations
        if fam in ('r1c', 'r3a', 'r3b', 'r3d', 'r3e', 'r3f', 'r3g', 'r4a', 'r4b', 'r4c', 'r5a', 'r6a'):
            it = combinations(range(m), k)
        else:
            it = permutations(range(m), k)
        for ps in it:
            sd = sides(fam, list(ps))
            if sd is not None:
                out.append((fam, list(ps), sd[0], sd[1]))
    return out
