"""Generate and replay PM-level certificates for all 54 EvenRS 8 relations.
PM-level moves (positions 0-based):
  ('H',i):  X_x X_y -> X_{xyx} X_x          ('Hi',i): X_x X_y -> X_y X_{yxy}
  ('C',i):  X_x X_x -> e                    ('I',i,z): e -> X_z X_z at i
  ('K',i):  X_x X_y -> X_{xy}  (x,y commuting, distinct, xy a PM)
  ('Ki',i,x,y): X_z -> X_x X_y  (x,y commuting, distinct, xy = z)
"""
from pm import mul, from_pairs, P8, PMS
from rs import rs_relations, fsym
import itertools, collections, sys

PMSET = set(PMS)


def c3(x, y):
    return mul(mul(x, y), x)


def commute(x, y):
    return mul(x, y) == mul(y, x)


def apply(mv, w):
    k, i = mv[0], mv[1]
    if k == 'H':
        x, y = w[i], w[i + 1]
        return w[:i] + (c3(x, y), x) + w[i + 2:]
    if k == 'Hi':
        x, y = w[i], w[i + 1]
        return w[:i] + (y, c3(y, x)) + w[i + 2:]
    if k == 'C':
        assert w[i] == w[i + 1]
        return w[:i] + w[i + 2:]
    if k == 'I':
        z = mv[2]
        return w[:i] + (z, z) + w[i:]
    if k == 'K':
        x, y = w[i], w[i + 1]
        assert x != y and commute(x, y) and mul(x, y) in PMSET
        return w[:i] + (mul(x, y),) + w[i + 2:]
    if k == 'Ki':
        x, y = mv[2], mv[3]
        assert x != y and commute(x, y) and mul(x, y) == w[i]
        return w[:i] + (x, y) + w[i + 1:]
    raise ValueError(k)


def run(moves, w):
    for mv in moves:
        w = apply(mv, w)
    return w


def dt(a, b, c, d):
    return from_pairs([(a, b), (c, d)])


def cf(delta):
    """Canonical factorization of a double transposition into commuting PMs (alpha, beta)."""
    moved = sorted(i for i in P8 if delta[i] != i)
    a = moved[0]
    b = delta[a]
    c = min(i for i in moved if i not in (a, b))
    d = delta[c]
    rest = sorted(set(P8) - set(moved))
    rho = [(rest[0], rest[1]), (rest[2], rest[3])]
    al = from_pairs([(a, c), (b, d)] + rho)
    be = from_pairs([(a, d), (b, c)] + rho)
    assert mul(al, be) == delta
    return (al, be)


def to_canon(w, i):
    """Moves turning the factorization (w[i], w[i+1]) of delta = w[i] w[i+1] into cf(delta)."""
    a, b = w[i], w[i + 1]
    delta = mul(a, b)
    al, be = cf(delta)
    if (a, b) == (al, be):
        return []
    if (a, b) == (be, al):
        return [('H', i)]
    supp = [x for x in P8 if delta[x] != x]
    mv = []
    if not all(a[x] == al[x] for x in supp):
        mv.append(('H', i))
        a, b = b, a
    cc = mul(a, be)
    assert commute(a, be) and cc in PMSET and commute(b, al) and mul(b, al) == cc
    mv += [('H', i), ('I', i + 2, be), ('K', i + 1), ('Ki', i + 1, b, al), ('C', i)]
    return mv


DTS = sorted({dt(*p) for p in itertools.permutations(P8, 4)})
DSET = set(DTS)
KL = collections.defaultdict(list)
for _x in DTS:
    for _y in DTS:
        if _x != _y and commute(_x, _y) and mul(_x, _y) in DSET:
            KL[mul(_x, _y)].append((_x, _y))


def dmoves(w):
    n = len(w)
    for i in range(n - 1):
        x, y = w[i], w[i + 1]
        yield ('DH', i), w[:i] + (c3(x, y), x) + w[i + 2:]
        yield ('DHi', i), w[:i] + (y, c3(y, x)) + w[i + 2:]
        if x == y:
            yield ('DC', i), w[:i] + w[i + 2:]
        elif commute(x, y) and mul(x, y) in DSET:
            yield ('DK', i), w[:i] + (mul(x, y),) + w[i + 2:]
    for i in range(n):
        for (x, y) in KL[w[i]]:
            yield ('DKi', i, x, y), w[:i] + (x, y) + w[i + 1:]


def _inverse_dmove(mv, w, v):
    """the dt-move taking v back to w (moves are invertible)."""
    if mv[0] == 'DC':
        return ('DI', mv[1], w[mv[1]])
    for mv2, u in dmoves(v):
        if u == w:
            return mv2
    raise RuntimeError('no inverse move')


def dsearch(a, b, maxlen=8, limit=5_000_000):
    """bidirectional BFS on dt words; returns a list of dt-moves from a to b."""
    a, b = tuple(a), tuple(b)
    if a == b:
        return []
    pa = {a: None}
    pb = {b: None}
    fa = [a]
    fb = [b]
    meet = None
    while (fa or fb) and meet is None and len(pa) + len(pb) < limit:
        if fa and (not fb or len(fa) <= len(fb)):
            nf = []
            for w in fa:
                for mv, v in dmoves(w):
                    if len(v) > maxlen or v in pa:
                        continue
                    pa[v] = (w, mv)
                    nf.append(v)
                    if v in pb:
                        meet = v
                        break
                if meet is not None:
                    break
            fa = nf
        else:
            nf = []
            for w in fb:
                for mv, v in dmoves(w):
                    if len(v) > maxlen or v in pb:
                        continue
                    pb[v] = (w, mv)
                    nf.append(v)
                    if v in pa:
                        meet = v
                        break
                if meet is not None:
                    break
            fb = nf
    if meet is None:
        return None
    path = []
    u = meet
    while pa[u] is not None:
        path.append(pa[u][1])
        u = pa[u][0]
    path.reverse()
    u = meet
    while pb[u] is not None:
        w, mv = pb[u]          # mv takes w to u; we need u -> w
        path.append(_inverse_dmove(mv, w, u))
        u = w
    return path


INSERT = False
KLP = collections.defaultdict(list)
for _x in PMS:
    for _y in PMS:
        if _x != _y and commute(_x, _y) and mul(_x, _y) in PMSET:
            KLP[mul(_x, _y)].append((_x, _y))


def pm_bfs(a, b, maxlen=8, limit=300000):
    a, b = tuple(a), tuple(b)
    if a == b:
        return []
    letters = set(a) | set(b)
    pa = {a: None}
    fa = [a]
    while fa and len(pa) < limit:
        nf = []
        for w in fa:
            n = len(w)
            cand = []
            for i in range(n - 1):
                cand += [('H', i), ('Hi', i)]
                if w[i] == w[i + 1]:
                    cand.append(('C', i))
                elif commute(w[i], w[i + 1]) and mul(w[i], w[i + 1]) in PMSET:
                    cand.append(('K', i))
            for i in range(n):
                for (x, y) in KLP[w[i]]:
                    cand.append(('Ki', i, x, y))
            if INSERT:
                for i in range(n + 1):
                    for z in letters:
                        cand.append(('I', i, z))
            for mv in cand:
                try:
                    v = apply(mv, w)
                except AssertionError:
                    continue
                if len(v) > maxlen or v in pa:
                    continue
                pa[v] = (w, mv)
                nf.append(v)
                if v == b:
                    path = []
                    u = v
                    while pa[u] is not None:
                        path.append(pa[u][1])
                        u = pa[u][0]
                    return list(reversed(path))
        fa = nf
    return None


def pmw(dw):
    return tuple(z for d in dw for z in cf(d))


def expand(dw, dpath):
    """Expand a dt-level path from dt-word dw into PM-level moves."""
    w = pmw(dw)
    moves = []
    cur = list(dw)
    for mv in dpath:
        k, i = mv[0], mv[1]
        p = 2 * i
        if k == 'DC':
            ms = [('H', p + 1), ('C', p), ('C', p)]
        elif k == 'DI':
            al, be = cf(mv[2])
            ms = [('I', p, be), ('I', p + 1, al), ('H', p)]
        elif k == 'DH':
            ms = [('H', p + 1), ('H', p), ('H', p + 2), ('H', p + 1)]
        elif k == 'DHi':
            ms = [('Hi', p + 1), ('Hi', p + 2), ('Hi', p), ('Hi', p + 1)]
        else:
            ms = None
        if ms is not None:
            w = run(ms, w)
            moves += ms
            if k in ('DH', 'DHi'):
                for j in (p, p + 2):
                    c = to_canon(w, j)
                    moves += c
                    w = run(c, w)
        else:
            if k == 'DK':
                seg = w[p:p + 4]
                tgt = cf(mul(cur[i], cur[i + 1]))
            else:
                seg = w[p:p + 2]
                tgt = cf(mv[2]) + cf(mv[3])
            path = pm_bfs(seg, tgt)
            assert path is not None, mv
            ms = [(m[0], m[1] + p) + tuple(m[2:]) for m in path]
            moves += ms
            w = run(ms, w)
        x = cur
        if k == 'DC':
            cur = x[:i] + x[i + 2:]
        elif k == 'DI':
            cur = x[:i] + [mv[2], mv[2]] + x[i:]
        elif k == 'DH':
            cur = x[:i] + [c3(x[i], x[i + 1]), x[i]] + x[i + 2:]
        elif k == 'DHi':
            cur = x[:i] + [x[i + 1], c3(x[i + 1], x[i])] + x[i + 2:]
        elif k == 'DK':
            cur = x[:i] + [mul(x[i], x[i + 1])] + x[i + 2:]
        else:
            cur = x[:i] + [mv[2], mv[3]] + x[i + 1:]
        assert w == pmw(cur), (mv, 'not canonical')
    return moves, w


AUX = (6, 7)


def PhiD(s):
    c, d = s
    if d >= 2:
        return [dt(0, 1, d, d + 1)]
    x = dt(1, 2, *AUX)
    y = dt(0, 1, *AUX)
    return [x, y] if not c else [y, x]


if __name__ == '__main__':
    for c in (False, True):
        for d in range(1, 7):
            p = tuple(P8)
            for z in PhiD((c, d)):
                p = mul(p, z)
            assert p == fsym(8, (c, d))
    total = 0
    mx = 0
    kinds = collections.Counter()
    for r in rs_relations(8):
        print(r[0], r[1], r[2], flush=True)
        L = [z for s in r[3] for z in PhiD(s)]
        R = [z for s in r[4] for z in PhiD(s)]
        dpath = dsearch(L, R)
        assert dpath is not None, r
        moves, w = expand(L, dpath)
        assert run(moves, pmw(L)) == pmw(R)
        total += len(moves)
        mx = max(mx, len(moves))
        for m in moves:
            kinds[m[0]] += 1
    print('all 54 relations certified at PM level; total moves', total, 'max per relation', mx)
    print('move kinds', dict(kinds))
