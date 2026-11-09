"""Data for the labels of the controlled A8: the 105 perfect matchings of
the eight Gray positions, the five base matchings (one per union type with
mu0), and for each matching m a base type k and a Coxeter word c whose
permutation commutes with mu0 and conjugates nu_k to m.

Conventions are Agda's: act w is the inverse action, act (u . v) = act u o
act v, act [s_d] = the transposition (d d+1); the matching of the frame of
G by a word F is act F o mu0 o act F^-1.
"""
import itertools
from collections import deque

MU0 = tuple(i ^ 1 for i in range(8))
GRAY = [0b000, 0b001, 0b011, 0b010, 0b110, 0b111, 0b101, 0b100]
POS = {s: i for i, s in enumerate(GRAY)}


def sw(d, i):
    return d + 1 if i == d else (d if i == d + 1 else i)


def act(w, i):
    for d in reversed(w):
        i = sw(d, i)
    return i


def act_t(w):
    return tuple(act(w, i) for i in range(8))


def compose(p, q):          # p o q
    return tuple(p[q[i]] for i in range(8))


def inverse(p):
    r = [0] * 8
    for i, x in enumerate(p):
        r[x] = i
    return tuple(r)


def match_of(w):
    a = act_t(w)
    return compose(compose(a, MU0), inverse(a))


def from_pairs(pairs):
    t = list(range(8))
    for a, b in pairs:
        t[a], t[b] = b, a
    return tuple(t)


def pairs_of(m):
    return sorted((i, m[i]) for i in range(8) if i < m[i])


def all_matchings():
    out = set()
    for perm in itertools.permutations(range(8)):
        if all(perm[2 * k] < perm[2 * k + 1] for k in range(4)):
            out.add(from_pairs([(perm[2 * k], perm[2 * k + 1]) for k in range(4)]))
    return sorted(out, key=lambda m: pairs_of(m))


PMS = all_matchings()
assert len(PMS) == 105
IDX = {m: i for i, m in enumerate(PMS)}


def plist(m):
    out = []
    for a, b in pairs_of(m):
        out += [a, b]
    return out


def words_by_perm():
    """A shortest Coxeter word for every permutation (BFS over act tables)."""
    start = tuple(range(8))
    prev = {start: None}
    dq = deque([start])
    while dq:
        t = dq.popleft()
        for d in range(7):
            nt = tuple(t[sw(d, i)] for i in range(8))     # act (w . [d]) = act w o sw d
            if nt not in prev:
                prev[nt] = (t, d)
                dq.append(nt)
    return prev


PREV = words_by_perm()


def word_of(t):
    w = []
    u = t
    while PREV[u] is not None:
        p, d = PREV[u]
        w.append(d)
        u = p
    w = list(reversed(w))
    assert act_t(w) == t
    return w


# Frames by state-level circuits Q: nu_k = Q mu0 Q^-1, in positions.
def state_conj(qfun):
    """Position matching of the frame Q G Q^-1 in diagram order (Q acts
    first): as a function Q^-1 o X0 o Q."""
    m = [None] * 8
    qi = {qfun(x): x for x in range(8)}
    for i in range(8):
        s = GRAY[i]
        y = qi[qfun(s) ^ 1]
        m[i] = POS[y]
    return tuple(m)


def cx(c, t):
    return lambda x: x ^ (((x >> c) & 1) << t)


def ccx(a, b, t):
    return lambda x: x ^ ((((x >> a) & (x >> b)) & 1) << t)


def seq(*fs):
    def f(x):
        for g in fs:
            x = g(x)
        return x
    return f


BASE_Q = [
    ('BC11', lambda x: x),
    ('BC22', cx(0, 1)),
    ('BC211', ccx(2, 0, 1)),
    ('BC31', seq(ccx(2, 0, 1), ccx(1, 0, 2))),
    ('BC4', seq(cx(0, 1), ccx(1, 0, 2))),
]
BASE = [state_conj(q) for _, q in BASE_Q]
BASE_IDX = [IDX[m] for m in BASE]

# The centraliser of mu0, as act tables.
CENT = [p for p in itertools.permutations(range(8))
        if all(p[MU0[x]] == MU0[p[x]] for x in range(8))]
assert len(CENT) == 384


def orbit_data():
    out = []
    for m in PMS:
        best = None
        for k, nu in enumerate(BASE):
            for c in CENT:
                if compose(compose(c, nu), inverse(c)) == m:
                    w = word_of(c)
                    if best is None or len(w) < len(best[1]):
                        best = (k, w)
        assert best is not None
        out.append(best)
    return out


ORBIT = orbit_data()

if __name__ == '__main__':
    print('base labels', BASE_IDX)
    from collections import Counter
    print('orbit sizes', Counter(k for k, _ in ORBIT))
    print('max orbit word', max(len(w) for _, w in ORBIT))
