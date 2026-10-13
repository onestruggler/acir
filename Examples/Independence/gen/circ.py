"""Circuits of a PROP fragment as letter lists, for finding engine steps.

A letter is (kind, wire): kind one of w (the scalar ω), H, S, T, CX, SW,
wire the lowest wire it acts on (None for the scalar).  Lists are in
diagram order (time order), as Examples.Independence.Engine reads them.
Wire 0 is the bottom wire; CX acts on (w, w+1) with control w+1 and
target w; SW swaps w and w+1.

The search: two letter lists are compared up to commuting letters (on
disjoint wires) by a normal form of their traces (canon); an equation is
applied wherever its left side occurs as a convex subtrace (occurrences),
the list rearranged to make it contiguous; find_steps is a bidirectional
breadth-first search over such rewrites, and agda_steps writes a path as
the engine's perm and rw steps.  Every line is also checked numerically
(same) before any search.
"""
import cmath, math, itertools
from collections import deque

ARITY = {'w': 0, 'm': 0, 'H': 1, 'S': 1, 'Z': 1, 'T': 1, 'X': 1, 'CX': 2, 'SW': 2}

# Real Clifford has Z as a gate, where Clifford spells it S S.
PRIMITIVE_Z = False


def wires(l):
    k, w = l
    a = ARITY[k]
    return frozenset() if a == 0 else frozenset(range(w, w + a))


def commute(a, b):
    return not (wires(a) & wires(b))


# ---------------------------------------------------------------------
# Abstract gates and their spelling
#
# An abstract gate is ('w',), ('H', w), ('S', w), ('CX', c, t) (control
# c, target t, any two wires) or ('SW', a, b) (a < b).  Each has one
# spelling in letters: gates on adjacent wires directly, the others
# conjugated by swaps.

def cx(c, t):
    """CNOT with control c and target t, spelled with adjacent letters."""
    if c == t + 1:
        return [('CX', t)]
    if t == c + 1:
        return [('SW', c), ('CX', c), ('SW', c)]
    if c == t + 2:
        return [('SW', t), ('CX', t + 1), ('SW', t)]
    if t == c + 2:
        return [('SW', c), ('SW', c + 1), ('CX', c + 1), ('SW', c + 1), ('SW', c)]
    raise ValueError((c, t))


def sw(a, b):
    a, b = min(a, b), max(a, b)
    if b == a + 1:
        return [('SW', a)]
    if b == a + 2:
        return [('SW', a), ('SW', a + 1), ('SW', a)]
    raise ValueError((a, b))


def spell1(g):
    if g[0] in ('w', 'm'):
        return [(g[0], None)]
    if g[0] in ('H', 'S', 'T', 'Z'):
        return [(g[0], g[1])]
    if g[0] == 'CX':
        return cx(g[1], g[2])
    if g[0] == 'SW':
        return sw(g[1], g[2])
    raise ValueError(g)


def spell(gs):
    out = []
    for g in gs:
        out += spell1(g)
    return out


def gwires(g):
    return set(g[1:])


def permute(g, pi):
    """The gate g with its wires renamed by pi (a function)."""
    if g[0] in ('w', 'm'):
        return g
    if g[0] in ('H', 'S', 'T', 'Z'):
        return (g[0], pi(g[1]))
    if g[0] == 'CX':
        return ('CX', pi(g[1]), pi(g[2]))
    a, b = pi(g[1]), pi(g[2])
    return ('SW', min(a, b), max(a, b))


def gshift(gs, s):
    return [permute(g, lambda w: w + s) for g in gs]


def gname(g):
    if g[0] == 'w':
        return 'ω'
    if g[0] == 'm':
        return '−'
    return g[0] + ''.join(str(x) for x in g[1:])


# The transcription notation, tokens in time order:  w  wd (ω⁷)  w2 …
# H0 S1 Z0 X0 Sd0 T0  CX10 (control 1 target 0) CX01 CX20 CX02 CX21 CX12
# SW01 SW12 SW02  CZ10 (the source's CZ: H on the lower wire around CX)

def gparse(s):
    out = []
    for tok in s.split():
        if tok == 'w':
            out.append(('w',))
        elif tok == 'm':
            out.append(('m',))
        elif PRIMITIVE_Z and tok[0] == 'Z' and tok[1:].isdigit():
            out.append(('Z', int(tok[1:])))
        elif PRIMITIVE_Z and tok[0] == 'X' and tok[1:].isdigit():
            k = int(tok[1:])
            out += [('H', k), ('Z', k), ('H', k)]
        elif tok.startswith('w') and tok[1:].isdigit():
            out += [('w',)] * int(tok[1:])
        elif tok == 'wd':
            out += [('w',)] * 7
        elif tok.startswith('Sd'):
            out += [('S', int(tok[2:]))] * 3
        elif tok[0] == 'Z' and tok[1:].isdigit():
            out += [('S', int(tok[1:]))] * 2
        elif tok[0] == 'X' and tok[1:].isdigit():
            k = int(tok[1:])
            out += [('H', k), ('S', k), ('S', k), ('H', k)]
        elif tok[0] in 'HST' and tok[1:].isdigit():
            out.append((tok[0], int(tok[1:])))
        elif tok.startswith('CX'):
            out.append(('CX', int(tok[2]), int(tok[3])))
        elif tok.startswith('CZ'):
            a, b = int(tok[2]), int(tok[3])
            lo = min(a, b)
            out += [('H', lo), ('CX', lo + 1, lo), ('H', lo)]
        elif tok.startswith('SW'):
            a, b = int(tok[2]), int(tok[3])
            out.append(('SW', min(a, b), max(a, b)))
        else:
            raise ValueError(tok)
    return out


def parse(s):
    return spell(gparse(s))


# ---------------------------------------------------------------------
# Semantics: matrices on 2^n basis states, bit k of the index = wire k

R2 = 1 / math.sqrt(2)
OMEGA = cmath.exp(1j * math.pi / 4)


def gate_matrix(l, n):
    k, w = l
    N = 1 << n
    M = [[0j] * N for _ in range(N)]
    for x in range(N):
        if k == 'w':
            M[x][x] = OMEGA
        elif k == 'm':
            M[x][x] = -1
        elif k == 'H':
            b = (x >> w) & 1
            y = x ^ (1 << w)
            M[x][x] += R2 * (-1 if b else 1)
            M[y][x] += R2
        elif k == 'S':
            M[x][x] = 1j if (x >> w) & 1 else 1
        elif k == 'T':
            M[x][x] = OMEGA if (x >> w) & 1 else 1
        elif k == 'Z':
            M[x][x] = -1 if (x >> w) & 1 else 1
        elif k == 'CX':
            y = x ^ (1 << w) if (x >> (w + 1)) & 1 else x
            M[y][x] = 1
        elif k == 'SW':
            b0, b1 = (x >> w) & 1, (x >> (w + 1)) & 1
            y = x & ~(3 << w) | (b1 << w) | (b0 << (w + 1))
            M[y][x] = 1
    return M


def mul(A, B):
    N = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(N)) for j in range(N)] for i in range(N)]


def unitary(c, n):
    N = 1 << n
    U = [[1 + 0j if i == j else 0j for j in range(N)] for i in range(N)]
    for l in c:
        U = mul(gate_matrix(l, n), U)       # diagram order: later gates on the left
    return U


def same(c1, c2, n, tol=1e-9):
    A, B = unitary(c1, n), unitary(c2, n)
    return all(abs(A[i][j] - B[i][j]) < tol for i in range(len(A)) for j in range(len(A)))


# ---------------------------------------------------------------------
# Traces: equality up to commuting letters

def key(l):
    k, w = l
    return (-1 if w is None else w, k)


def canon(c):
    """The lexicographically least topological order (a normal form)."""
    n = len(c)
    preds = [set(j for j in range(i) if not commute(c[j], c[i])) for i in range(n)]
    done = [False] * n
    out = []
    for _ in range(n):
        best = None
        for i in range(n):
            if not done[i] and all(done[j] for j in preds[i]):
                if best is None or key(c[i]) < key(c[best]):
                    best = i
        done[best] = True
        out.append(c[best])
    return tuple(out)


# ---------------------------------------------------------------------
# Occurrences of a pattern up to commutation

def occurrences(c, pat):
    """Ways to find pat (a list) as a convex subtrace of c.  Yields the
    rearranged list c' in which pat sits contiguously at position i,
    together with i."""
    m = len(pat)
    if m == 0:
        for i in range(len(c) + 1):
            yield list(c), i
        return
    n = len(c)

    def extend(sel, j):
        if j == m:
            yield list(sel)
            return
        for p in range(n):
            if p in sel or c[p] != pat[j]:
                continue
            # order of dependent pattern letters must be kept
            # identical letters are interchangeable: take them in order
            ok = True
            for jj in range(j):
                if (not commute(pat[jj], pat[j]) or pat[jj] == pat[j]) and sel[jj] > p:
                    ok = False
                    break
            if ok:
                yield from extend(sel + [p], j + 1)

    seen = set()
    for sel in extend([], 0):
        S = set(sel)
        lo, hi = min(sel), max(sel)
        # between lo and hi: non-selected letters go left or right
        left, right = [], []
        okc = True
        for p in range(lo, hi + 1):
            if p in S:
                continue
            z = c[p]
            dep_before = any(q < p and not commute(c[q], z) for q in S) or \
                any(not commute(c[q], z) for q in right)
            if dep_before:
                if any(q > p and not commute(c[q], z) for q in S):
                    okc = False
                    break
                right.append(p)
            else:
                left.append(p)
        if not okc:
            continue
        # letters before lo and after hi stay; the pattern in pat order
        # (sel is in pat order; dependent pairs keep their order)
        new = [c[p] for p in range(lo)] + [c[p] for p in left] + [c[p] for p in sel] + \
            [c[p] for p in right] + [c[p] for p in range(hi + 1, n)]
        i = lo + len(left)
        t = (tuple(new), i)
        if t not in seen and canon(new) == canon(c):
            seen.add(t)
            yield new, i


# ---------------------------------------------------------------------
# Equations


class Eq:
    """A named equation lhs = rhs on wires 0 .. arity-1 (an Agda Eqn)."""
    def __init__(self, name, arity, lhs, rhs):
        self.name, self.arity, self.lhs, self.rhs = name, arity, lhs, rhs

    def __repr__(self):
        return self.name


class Inst:
    """An equation used in a direction (fwd: lhs -> rhs) at a shift."""
    def __init__(self, eq, fwd, s):
        self.eq, self.fwd, self.s = eq, fwd, s
        sh = lambda c: [(k, None if w is None else w + s) for k, w in c]
        self.l = sh(eq.lhs if fwd else eq.rhs)
        self.r = sh(eq.rhs if fwd else eq.lhs)

    def flip(self):
        return Inst(self.eq, not self.fwd, self.s)

    def expr(self):
        e = self.eq.name
        for _ in range(self.s):
            e = 'lift⁼ ' + par(e)
        return e if self.fwd else 'sym⁼ ' + par(e)


def par(e):
    return e if ' ' not in e else '(' + e + ')'


def instances(eqs, width, inserting=None):
    """All placements, both ways; a pure insertion (an empty side read as
    the left) only for the equations in `inserting` (default: all)."""
    out = []
    for e in eqs:
        shifts = [0] if e.arity == 0 else range(0, width - e.arity + 1)
        for s in shifts:
            for fwd in (True, False):
                ins = Inst(e, fwd, s)
                if ins.l or inserting is None or e.name in inserting:
                    out.append(ins)
    return out


def rewrites(c, insts):
    """One rewrite: (inst, rearranged c, position, result)."""
    for ins in insts:
        for c2, i in occurrences(c, ins.l):
            yield ins, c2, i, c2[:i] + ins.r + c2[i + len(ins.l):]


def _search(a, b, insts, depth, maxstates):
    """Bidirectional breadth-first search on traces.  A path is a list of
    (inst, before, i, after), `before` the list the rewrite applies to."""
    ka, kb = canon(a), canon(b)
    if ka == kb:
        return []
    # parent links: key -> (prev key, step) ; step maps prev -> this
    pa = {ka: None}
    pb = {kb: None}
    fa = [tuple(a)]
    fb = [tuple(b)]
    rep = {ka: tuple(a), kb: tuple(b)}

    def expand(front, par_, other):
        nxt = []
        for c in front:
            kc = canon(c)
            for ins, c2, i, new in rewrites(list(c), insts):
                k = canon(new)
                if k in par_:
                    continue
                par_[k] = (kc, (ins, list(c2), i, list(new)))
                rep.setdefault(k, tuple(new))
                if k in other:
                    return k, nxt
                nxt.append(tuple(new))
                if len(pa) + len(pb) > maxstates:
                    raise OverflowError
        return None, nxt

    for d in range(depth):
        side_a = len(fa) <= len(fb)
        try:
            if side_a:
                meet, fa = expand(fa, pa, pb)
            else:
                meet, fb = expand(fb, pb, pa)
        except OverflowError:
            return None
        if meet is not None:
            # a ... meet
            left = []
            k = meet
            while pa[k] is not None:
                pk, st = pa[k]
                left.append(st)
                k = pk
            left.reverse()
            # meet ... b: reverse the b-side steps
            right = []
            k = meet
            while pb[k] is not None:
                pk, (ins, before, i, after) = pb[k]
                right.append((ins.flip(), after, i, before))
                k = pk
            return left + right
        if not fa and not fb:
            return None
    return None


def find_steps(a, b, eqs, width, depth=4, maxstates=300000, inserting=None):
    return _search(a, b, instances(eqs, width, inserting), depth, maxstates)


# ---------------------------------------------------------------------
# Agda output

def letter(l):
    k, w = l
    base = {'w': 'ωₗ', 'm': 'mₗ', 'H': 'Hₗ', 'S': 'Sₗ', 'Z': 'Zₗ', 'T': 'Tₗ', 'CX': 'CXₗ',
            'SW': 'σₗ'}[k]
    return base if w is None else base + ' ↥' * w


def agda_list(c):
    return '(' + ' ∷ '.join(letter(l) for l in c) + (' ∷ [])' if c else '[])')


def agda_steps(a, b, path):
    steps = []
    cur = list(a)
    for ins, before, i, after in path:
        if before != cur:
            assert canon(before) == canon(cur)
            steps.append('perm ' + agda_list(before))
        assert before[i:i + len(ins.l)] == ins.l
        steps.append('rw %d %s' % (i, par(ins.expr())))
        cur = after
    if cur != list(b):
        assert canon(cur) == canon(b)
        steps.append('perm ' + agda_list(b))
    return steps
