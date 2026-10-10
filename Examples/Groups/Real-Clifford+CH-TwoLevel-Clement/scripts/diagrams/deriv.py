"""Derivation search for Real-Clifford+CH-TwoLevel words (mirrors the
generic Engine.agda).  Letters: ('Z',a), ('X',a,b), ('H',a,b) with a<b;
lists in operator order (the head acts last), as words."""
import itertools, sys
from collections import deque, Counter

sys.path.insert(0, '..')

def idx(g):
    return set(g[1:])

def comm(x, y):
    return not (idx(x) & idx(y))

def code(g, n):
    if g[0] == 'Z':
        return 3 * g[1]
    if g[0] == 'X':
        return 1 + 3 * (g[1] + n * g[2])
    return 2 + 3 * (g[1] + n * g[2])

def canonical(xs, n):
    def less(x, y):
        return code(x, n) < code(y, n)
    def insert(x, xs):
        ys, zs = [], list(xs)
        while zs and comm(x, zs[0]):
            ys.insert(0, zs[0]); zs = zs[1:]
        while ys and less(x, ys[0]):
            zs.insert(0, ys[0]); ys = ys[1:]
        return list(reversed(ys)) + [x] + zs
    out = []
    for x in reversed(xs):
        out = insert(x, out)
    return tuple(out)

def check_equiv(a, b, n):
    return canonical(a, n) == canonical(b, n)

# ---------------------------------------------------------------------
# Exact matrices (Z[sqrt2]/sqrt2^E), for checking.

def zadd(x, y): return (x[0] + y[0], x[1] + y[1])
def zmul(x, y): return (x[0] * y[0] + 2 * x[1] * y[1], x[0] * y[1] + x[1] * y[0])

def ident(m):
    return (0, tuple(tuple(((1, 0) if i == j else (0, 0)) for j in range(m)) for i in range(m)))

def norm(P):
    E, M = P
    while E > 0 and all(not (x[0] & 1) for row in M for x in row):
        M = tuple(tuple((x[1], x[0] // 2) for x in row) for row in M)
        E -= 1
    return (E, M)

def gen(g, m):
    E, I = ident(m)
    rows = [list(r) for r in I]
    if g[0] == 'Z':
        rows[g[1]][g[1]] = (-1, 0)
        return (0, tuple(map(tuple, rows)))
    a, b = g[1], g[2]
    if g[0] == 'X':
        rows[a][a] = (0, 0); rows[b][b] = (0, 0); rows[a][b] = (1, 0); rows[b][a] = (1, 0)
        return (0, tuple(map(tuple, rows)))
    rows = [[(0, 2 * 0) for _ in range(m)] for _ in range(m)]
    for i in range(m):
        rows[i][i] = (0, 1)        # sqrt2 on the diagonal (scaled by sqrt2^1)
    rows[a][a] = (1, 0); rows[a][b] = (1, 0); rows[b][a] = (1, 0); rows[b][b] = (-1, 0)
    return (1, tuple(map(tuple, rows)))

def mul(P, Q):
    (E1, A), (E2, B) = P, Q
    m = len(A)
    C = []
    for i in range(m):
        row = []
        for j in range(m):
            s = (0, 0)
            for l in range(m):
                s = zadd(s, zmul(A[i][l], B[l][j]))
            row.append(s)
        C.append(tuple(row))
    return norm((E1 + E2, tuple(C)))

def mat(word, m):
    P = ident(m)
    for g in word:
        P = mul(P, gen(g, m))
    return P

def same(l, r, m):
    return mat(l, m) == mat(r, m)

# ---------------------------------------------------------------------
# Local axioms (a1)-(d2) of Figure 6 in dimension m (commutations are perm).

def local_axioms(m):
    R = range(m)
    out = []
    Z = lambda a: ('Z', a)
    X = lambda a, b: ('X', a, b)
    H = lambda a, b: ('H', a, b)
    for a in R:
        out.append(('a1-%d' % a, [Z(a), Z(a)], [], ('a1', a)))
    for a, b in itertools.combinations(R, 2):
        out.append(('a2-%d%d' % (a, b), [X(a, b), X(a, b)], [], ('a2', a, b)))
        out.append(('a3-%d%d' % (a, b), [H(a, b), H(a, b)], [], ('a3', a, b)))
        out.append(('c1-%d%d' % (a, b), [Z(a), X(a, b)], [X(a, b), Z(b)], ('c1', a, b)))
        out.append(('d1-%d%d' % (a, b), [Z(a), Z(b), H(a, b)], [H(a, b), Z(a), Z(b)], ('d1', a, b)))
        out.append(('d2-%d%d' % (a, b), [Z(b), H(a, b)], [H(a, b), X(a, b)], ('d2', a, b)))
    for a, b, c in itertools.combinations(R, 3):
        out.append(('c2-%d%d%d' % (a, b, c), [X(b, c), X(a, b)], [X(a, b), X(a, c)], ('c2', a, b, c)))
        out.append(('c3-%d%d%d' % (a, b, c), [X(a, c), X(b, c)], [X(b, c), X(a, b)], ('c3', a, b, c)))
        out.append(('c4-%d%d%d' % (a, b, c), [H(b, c), X(a, b)], [X(a, b), H(a, c)], ('c4', a, b, c)))
        out.append(('c5-%d%d%d' % (a, b, c), [H(a, c), X(b, c)], [X(b, c), H(a, b)], ('c5', a, b, c)))
    return out

# ---------------------------------------------------------------------
# Occurrences of a pattern modulo commutation (from the CCX tool).

def occurrences(w, u):
    n, m = len(w), len(u)
    if m == 0:
        for i in range(n + 1):
            yield w[:i], [], w[i:]
        return
    def rec(i, used, pos):
        if i == m:
            yield list(pos)
            return
        for q in range(n):
            if q in used or w[q] != u[i]:
                continue
            ok = True
            for j in range(i):
                if not comm(u[j], u[i]) and not (pos[j] < q):
                    ok = False; break
            if ok:
                yield from rec(i + 1, used | {q}, pos + [q])
    seen = set()
    for pos in rec(0, frozenset(), []):
        S = set(pos)
        hi = max(pos)
        side = {}
        conflict = False
        for q in range(n):
            if q in S:
                continue
            left = any((not comm(w[q], w[s])) and q < s for s in pos)
            right = any((not comm(w[q], w[s])) and q > s for s in pos)
            if left and right:
                conflict = True; break
            if left:
                side[q] = 'x'
            elif right:
                side[q] = 'y'
        if conflict:
            continue
        def propagate(side):
            changed = True
            while changed:
                changed = False
                for q in range(n):
                    if q in S or q not in side:
                        continue
                    for q2 in range(n):
                        if q2 in S or q2 == q or comm(w[q], w[q2]):
                            continue
                        if side[q] == 'y' and q < q2:
                            if side.get(q2) == 'x':
                                return None
                            if q2 not in side:
                                side[q2] = 'y'; changed = True
                        if side[q] == 'x' and q2 < q:
                            if side.get(q2) == 'y':
                                return None
                            if q2 not in side:
                                side[q2] = 'x'; changed = True
            return side
        side = propagate(dict(side))
        if side is None:
            continue
        for q in range(n):
            if q in S or q in side:
                continue
            trial = dict(side); trial[q] = 'x' if q < hi else 'y'
            t2 = propagate(trial)
            if t2 is None:
                trial = dict(side); trial[q] = 'y' if q < hi else 'x'
                t2 = propagate(trial)
                if t2 is None:
                    side = None; break
            side = t2
        if side is None:
            continue
        x = [w[q] for q in range(n) if q not in S and side[q] == 'x']
        y = [w[q] for q in range(n) if q not in S and side[q] == 'y']
        key = (tuple(x), tuple(y))
        if key in seen:
            continue
        seen.add(key)
        yield x, u, y

class Lib:
    def __init__(self, n):
        self.n = n
        self.eqs = []
        self.counts = {}
        self.byname = {}
    def add(self, name, lhs, rhs, both=True):
        self.eqs.append((name, list(lhs), list(rhs)))
        self.byname[name] = (list(lhs), list(rhs))
        if both:
            nm = '(sym⁼ %s)' % name
            self.eqs.append((nm, list(rhs), list(lhs)))
            self.byname[nm] = (list(rhs), list(lhs))

def moves(w, lib, maxlen, alphabet=()):
    cw = Counter(w)
    for name, l, r in lib.eqs:
        if l:
            cl = lib.counts.get(name)
            if cl is None:
                cl = Counter(l); lib.counts[name] = cl
            if any(cw[g] < k for g, k in cl.items()):
                continue
        if not l:
            if r and r[0] in alphabet and len(w) + len(r) <= maxlen:
                for i in range(len(w) + 1):
                    yield (list(w), i, name, w[:i] + r + w[i:])
            continue
        if len(w) - len(l) + len(r) > maxlen:
            continue
        for x, u, y in occurrences(w, l):
            yield (x + u + y, len(x), name, x + r + y)

def search(start, goal, lib, maxdepth=6, maxlen=None, limit=200000, alphabet=None):
    n = lib.n
    if maxlen is None:
        maxlen = max(len(start), len(goal)) + 4
    if alphabet is None:
        alphabet = set(start) | set(goal)
    gkey = canonical(goal, n); skey = canonical(start, n)
    if skey == gkey:
        return []
    fwd = {skey: None}; bwd = {gkey: None}
    fq = deque([(list(start), 0)]); bq = deque([(list(goal), 0)])
    count = 0
    def path(par, key):
        out = []
        while par[key] is not None:
            prev, arr, i, name, new = par[key]
            out.append((prev, arr, i, name, new))
            key = canonical(prev, n)
        return list(reversed(out))
    while fq or bq:
        for q, par, other, sgn in ((fq, fwd, bwd, 1), (bq, bwd, fwd, -1)):
            if not q:
                continue
            depthnow = q[0][1]
            while q and q[0][1] == depthnow:
                w, dpt = q.popleft()
                if dpt >= maxdepth:
                    continue
                for arr, i, name, new in moves(w, lib, maxlen, alphabet):
                    key = canonical(new, n)
                    count += 1
                    if count > limit:
                        return None
                    if key in par:
                        continue
                    par[key] = (w, arr, i, name, new)
                    if key in other:
                        p1 = path(fwd, key); p2 = path(bwd, key)
                        steps = []
                        for (prev, arr0, i0, name0, new0) in p1:
                            steps.append(('perm', arr0)); steps.append(('rw', i0, name0, new0))
                        for (prev, arr0, i0, name0, new0) in reversed(p2):
                            inv = name0[6:-1] if name0.startswith('(sym⁼ ') else '(sym⁼ %s)' % name0
                            l, r = lib.byname[name0]
                            x = arr0[:i0]; y = arr0[i0 + len(l):]
                            steps.append(('perm', x + r + y)); steps.append(('rw', i0, inv, x + l + y))
                        return steps
                    q.append((new, dpt + 1))
    return None

def verify(start, goal, steps, lib):
    n = lib.n
    cur = list(start)
    for st in steps:
        if st[0] == 'perm':
            assert check_equiv(cur, st[1], n), ('bad perm', cur, st[1])
            cur = list(st[1])
        else:
            _, i, name, new = st
            l, r = lib.byname[name]
            assert cur[i:i + len(l)] == l, ('bad rw', cur, i, name)
            cur = cur[:i] + r + cur[i + len(l):]
    assert check_equiv(cur, goal, n)
    return cur

def rev(xs):
    return list(reversed(xs))

def relator(l, r):
    return list(l) + rev(r)

def rot(l, r, k, mlen):
    """rot⁼ k m: relator l r^-1 rotated by k, split after m: (take m, rev (drop m))."""
    rl = relator(l, r)
    rr = rl[k:] + rl[:k]
    return rr[:mlen], rev(rr[mlen:])

class Deriver:
    def __init__(self, m):
        self.m = m
        self.lib = Lib(m)
        for name, l, r, tag in local_axioms(m):
            self.lib.add(name, l, r)
        self.derived = []
    def add_eq(self, name, l, r, both=True):
        assert same(l, r, self.m), name
        self.lib.add(name, l, r, both)
    def derive(self, name, l, r, waypoints=(), maxdepth=6, maxlen=None, limit=4000000, alphabet=None, add=True):
        assert same(l, r, self.m), name
        pts = [list(l)] + [list(p) for p in waypoints] + [list(r)]
        for a, b in zip(pts, pts[1:]):
            assert same(a, b, self.m), ('waypoint not equal', name, a, b)
        steps = []
        for a, b in zip(pts, pts[1:]):
            st = search(a, b, self.lib, maxdepth=maxdepth, maxlen=maxlen, limit=limit, alphabet=alphabet)
            if st is None:
                raise RuntimeError('no derivation for %s segment %s -> %s' % (name, a, b))
            steps += st
            steps.append(('perm', list(b)))
        verify(l, r, steps, self.lib)
        self.derived.append((name, list(l), list(r), steps))
        if add:
            self.lib.add(name, l, r)
        print(name, 'steps', len(steps), file=sys.stderr, flush=True)
        return steps
