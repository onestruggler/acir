"""CliffCS₂ on two wires, at the level of blocks: the decoding of Bian and Selinger's
generators in dimension 4 (`dB`), the canonical words of S₄, the stabiliser words of the
atoms, the permutations transporting each relation from its standard instance, and the
certificates (rewriting steps over the block relations `cs2blk.BREL`) that the Lean
development `CliffordCS/W2Blocks.lean` checks."""
import itertools
from collections import deque
import numpy as np
import cs2blk as K

RN = list(K.BREL)                    # rule order = index in Lean's `brels`
RULES = [(tuple(K.BREL[n][0]), tuple(K.BREL[n][1])) for n in RN]
PERMB = ['t0', 't1', 't2', 'x0', 'x1']
ACT = {'t0': (1, 0, 2, 3), 't1': (0, 2, 1, 3), 't2': (0, 1, 3, 2), 'x0': (1, 0, 3, 2), 'x1': (2, 3, 0, 1)}

def actW(u):
    """The permutation of an operator-order word of permutation blocks (the last block acts
    first): actW(u)[x]."""
    p = (0, 1, 2, 3)
    for b in reversed(u):
        a = ACT.get(b, (0, 1, 2, 3))
        p = tuple(a[p[x]] for x in range(4))
    return p

key = actW

# --- canonical words of S₄ over t0, t1, t2 (shortest, first found by BFS appending letters)
def canon_words():
    seen = {key([]): []}
    dq = deque([[]])
    while dq:
        w = dq.popleft()
        for b in ['t0', 't1', 't2']:
            w2 = w + [b]
            k = key(w2)
            if k not in seen:
                seen[k] = w2; dq.append(w2)
    return [seen[k] for k in sorted(seen, key=lambda k: (len(seen[k]), seen[k]))]
CANON = canon_words()
assert len(CANON) == 24 and CANON[0] == []

def canon(u):
    k = key(u)
    for c in CANON:
        if key(c) == k: return c
    raise Exception(u)

# --- block-level rewriting
def apply(w, step):
    i, k, d = step
    l, r = RULES[k]
    a, b = (l, r) if d else (r, l)
    assert tuple(w[i:i + len(a)]) == a, (w, step, a)
    return tuple(w[:i]) + b + tuple(w[i + len(a):])

def run(w, steps):
    w = tuple(w)
    for st in steps: w = apply(w, st)
    return w

def moves(w, allowed, maxlen):
    for k in allowed:
        l, r = RULES[k]
        for (a, b, d) in ((l, r, True), (r, l, False)):
            if len(w) - len(a) + len(b) > maxlen: continue
            if not a:
                for i in range(len(w) + 1):
                    yield (i, k, d), w[:i] + b + w[i:]
                continue
            for i in range(len(w) - len(a) + 1):
                if w[i:i + len(a)] == a:
                    yield (i, k, d), w[:i] + b + w[i + len(a):]

def inv(steps):
    return [(i, k, not d) for (i, k, d) in reversed(steps)]

def bfs(u, v, names, maxdepth=8, maxlen=None, maxnodes=2 * 10 ** 6):
    allowed = [RN.index(n) for n in names]
    u, v = tuple(u), tuple(v)
    maxlen = maxlen or max(len(u), len(v)) + 4
    if u == v: return []
    fw = {u: None}; bw = {v: None}
    qf, qb = deque([u]), deque([v])
    for depth in range(maxdepth):
        if len(qf) <= len(qb):
            nq = deque()
            for w in qf:
                for st, w2 in moves(w, allowed, maxlen):
                    if w2 not in fw:
                        fw[w2] = (w, st); nq.append(w2)
                        if w2 in bw: return path(fw, bw, w2)
            qf = nq
        else:
            nq = deque()
            for w in qb:
                for st, w2 in moves(w, allowed, maxlen):
                    if w2 not in bw:
                        bw[w2] = (w, st); nq.append(w2)
                        if w2 in fw: return path(fw, bw, w2)
            qb = nq
        if len(fw) + len(bw) > maxnodes: break
    raise Exception('no path %s -> %s' % (u, v))

def path(fw, bw, m):
    a = []
    x = m
    while fw[x] is not None:
        y, st = fw[x]; a.append(st); x = y
    a.reverse()
    b = []
    x = m
    while bw[x] is not None:
        y, st = bw[x]; b.append(st); x = y        # st takes y to x
    return a + inv_list(b)

def inv_list(b):
    # b[j] takes y_j to x_j where x_0 = m; we need the steps from m onwards: x_j -> y_j
    return [(i, k, not d) for (i, k, d) in b]

def through(lines, names, **kw):
    """Steps through a list of block lines, each step a BFS with the given rules."""
    steps = []
    for a, b in zip(lines, lines[1:]):
        st = bfs(a, b, names, **kw)
        assert run(a, st) == tuple(b)
        steps += st
    assert run(lines[0], steps) == tuple(lines[-1])
    return steps

def B(s): return s.split()

# --- canonical steps: c ++ [b] -> canon(c ++ [b])
COX = ['P00', 'P11', 'P22', 'P02', 'P010', 'P121', 'PX0', 'PX1', 'X00', 'X11']
def canon_certs():
    out = {}
    for c in CANON:
        for b in PERMB:
            w = c + [b]
            out[(tuple(c), b)] = bfs(w, canon(w), COX, maxdepth=10)
    return out

# --- atoms, bases, stabilisers
ATOMS = {'t2': ['t0', 't2'], 'ck': ['t0'], 'cs': ['t0', 't1']}
def base_ok(A, k, k2):
    if A == 'cs': return k[3] == k2[3]
    if A == 'ck': return k[2] == k2[2] and k[3] == k2[3]
    return {k[2], k[3]} == {k2[2], k2[3]}

def stab_table(A):
    letters = ATOMS[A]
    seen = {key([]): []}
    dq = deque([[]])
    while dq:
        w = dq.popleft()
        for b in letters:
            w2 = w + [b]; kk = key(w2)
            if kk not in seen: seen[kk] = w2; dq.append(w2)
    return seen

def stabW(A, k):
    return STAB[A].get(k, [])
STAB = {A: stab_table(A) for A in ATOMS}

def check_frame():
    for A in ATOMS:
        for c in CANON:
            for c2 in CANON:
                if base_ok(A, key(c), key(c2)):
                    V = stabW(A, key(list(reversed(c)) + c2))
                    assert all(b in ATOMS[A] for b in V)
                    assert key(c + V) == key(c2), (A, c, c2)

# --- the decoding
QI = {3: [], 2: ['x0'], 1: ['x1'], 0: ['x1', 'x0']}
QP = {(2, 3): [], (0, 1): ['x1'], (0, 2): ['t1', 'x1'], (1, 3): ['t1'], (0, 3): ['t0', 't1'], (1, 2): ['t2', 't1']}
for a in QI: assert key(QI[a])[3] == a
for (a, b), q in QP.items(): assert key(q)[2] == a and key(q)[3] == b

def dB(g):
    if g[0] == 'w': return ['w']
    if g[0] == 'i': q, A = QI[g[1]], 'cs'
    else: q, A = QP[(g[1], g[2])], {'X': 't2', 'K': 'ck'}[g[0]]
    return q + [A] + list(reversed(q))

def DBs(gs):
    out = []
    for g in gs: out += dB(g)
    return out

def atom(g): return {'X': 't2', 'K': 'ck', 'i': 'cs'}[g[0]]
def Qof(g): return QI[g[1]] if g[0] == 'i' else QP[(g[1], g[2])]

def okG(P, g0, g):
    if g0[0] != g[0]: return False
    return base_ok(atom(g0), key(P + Qof(g0)), key(Qof(g)))

def Pw(std, targets):
    for c in CANON:
        p = key(c)
        if all(p[s] == t for s, t in zip(std, targets)): return c
    return []

if __name__ == '__main__':
    import cs2w
    for a in range(4):
        g = ('i', a); assert np.allclose(K.mat(dB(g)), cs2w.gen_mat(g)), g
    for (a, b) in QP:
        for t in 'XK':
            g = (t, a, b); assert np.allclose(K.mat(dB(g)), cs2w.gen_mat(g)), g
    check_frame()
    cc = canon_certs()
    print('canon certs', sum(len(v) for v in cc.values()), 'steps, max', max(len(v) for v in cc.values()))
    print('ok')

# --- w-canonical BFS: scalars moved to the front after every move
WI = {b: RN.index('W' + b) for b in K.BLK if b != 'w'}
def wcanon(w):
    """Steps moving every w of w to the front (rule 'W b' read backwards: b w -> w b)."""
    w = list(w); steps = []
    changed = True
    while changed:
        changed = False
        for i in range(len(w) - 1):
            if w[i] != 'w' and w[i + 1] == 'w':
                steps.append((i, WI[w[i]], False)); w[i], w[i + 1] = 'w', w[i]; changed = True
    return tuple(w), steps

def bfsw(u, v, names, maxdepth=8, maxlen=None, maxnodes=2 * 10 ** 6):
    allowed = [RN.index(n) for n in names]
    u0, su = wcanon(u); v0, sv = wcanon(v)
    maxlen = maxlen or max(len(u0), len(v0)) + 4
    if u0 == v0: return su + inv(sv)
    fw = {u0: None}; bw = {v0: None}
    qf, qb = deque([u0]), deque([v0])
    def nbrs(w):
        for st, w2 in moves(w, allowed, maxlen):
            w3, s3 = wcanon(w2)
            yield [st] + s3, w3
    def build(m):
        a = []; x = m
        while fw[x] is not None:
            y, st = fw[x]; a = st + a; x = y
        b = []; x = m
        while bw[x] is not None:
            y, st = bw[x]; b = b + inv(st); x = y
        return a + b
    for depth in range(maxdepth):
        if len(qf) <= len(qb):
            nq = deque()
            for w in qf:
                for st, w2 in nbrs(w):
                    if w2 not in fw:
                        fw[w2] = (w, st); nq.append(w2)
                        if w2 in bw: return su + build(w2) + inv(sv)
            qf = nq
        else:
            nq = deque()
            for w in qb:
                for st, w2 in nbrs(w):
                    if w2 not in bw:
                        bw[w2] = (w, st); nq.append(w2)
                        if w2 in fw: return su + build(w2) + inv(sv)
            qb = nq
        if len(fw) + len(bw) > maxnodes: break
    raise Exception('no path %s -> %s' % (u, v))

def thru(lines, names, **kw):
    steps = []
    for a, b in zip(lines, lines[1:]):
        st = bfsw(a, b, names, **kw)
        assert run(a, st) == tuple(b), (a, b)
        steps += st
    return steps

def G(*xs):
    """A generator from its name and indices."""
    return tuple(xs)

ALLR = [n for n in RN]
STD = {   # family -> (std lhs gens, std rhs gens, lines (block words) or None, rules)
  'r1': ([G('i', 3)] * 4, [], None, ['CS4']),
  'r3': ([G('K', 2, 3)] * 8, [], [B('ck ' * 8), B('s1 ' * 12), []], ['CK2', 'S14']),
  'r4': ([G('i', 2), G('i', 3)], [G('i', 3), G('i', 2)],
         [B('x0 cs x0 cs'), B('s1 cs cs cs cs'), B('s1'), B('s1 cs cs cs cs'), B('cs s1 cs cs cs'), B('cs x0 cs x0')],
         ['I2', 'CS4', 'S1CS']),
  'r6': ([G('i', 1), G('K', 2, 3)], [G('K', 2, 3), G('i', 1)],
         [B('x1 cs x1 ck'), B('s0 cs cs cs ck'), B('ck s0 cs cs cs'), B('ck x1 cs x1')], ['I1', 'NS']),
  'r9': ([G('K', 0, 1), G('K', 2, 3)], [G('K', 2, 3), G('K', 0, 1)],
         [B('x1 ck x1 ck'), B('w w w w w w w h0'), B('ck x1 ck x1')], ['KK0', 'X11', 'X1H0']),
  'r15': ([G('K', 2, 3), G('i', 3), G('i', 3)], [G('X', 2, 3), G('K', 2, 3)], None, ['R15']),
  'r16': ([G('K', 2, 3)] + [G('i', 3)] * 3, [G('i', 3), G('K', 2, 3), G('i', 3), G('K', 2, 3)], None, ['R16']),
  'r17': ([G('K', 2, 3), G('i', 2), G('i', 3)], [G('i', 2), G('i', 3), G('K', 2, 3)],
          [B('ck x0 cs x0 cs'), B('ck s1 cs cs cs cs'), B('ck s1'), B('s1 ck'), B('s1 cs cs cs cs ck'),
           B('x0 cs x0 cs ck')], ['I2', 'CS4', 'S1CK']),
  'r18': ([G('K', 2, 3), G('K', 2, 3), G('i', 2), G('i', 3)], [],
          [B('ck ck x0 cs x0 cs'), B('ck ck s1 cs cs cs cs'), B('ck ck s1'), B('s1 s1 s1 s1'), []],
          ['I2', 'CS4', 'CK2', 'S14']),
  'r19': ([G('K', 0, 1), G('K', 2, 3), G('K', 0, 2), G('K', 1, 3)],
          [G('K', 0, 2), G('K', 1, 3), G('K', 0, 1), G('K', 2, 3)],
          [B('x1 ck x1 ck t1 x1 ck x1 t1 t1 ck t1'), B('x1 ck x1 ck t1 x1 ck x1 ck t1'),
           B('w w w w w w w h0 t1 x1 ck x1 ck t1'), B('w w w w w w w h0 t1 w w w w w w w h0 t1'),
           B('w w w w w w w w w w w w w w h0 h1'), B('w w w w w w w w w w w w w w h1 h0'),
           B('w w w w w w w w w w w w w w t1 h0 t1 h0'), B('w w w w w w w t1 x1 ck x1 ck t1 h0'),
           B('t1 x1 ck x1 ck t1 x1 ck x1 ck'), B('t1 x1 ck x1 t1 t1 ck t1 x1 ck x1 ck')],
          ['KK0', 'P11', 'T1H0', 'H01']),
}
SQ_LINES = [B('w w'), B('x1 s1 x1 s1'), B('x1 s1 x1 s1 cs cs cs cs'), B('x1 s1 x1 x0 cs x0 cs'),
            B('x1 s1 cs cs cs cs x1 x0 cs x0 cs'), B('x1 x0 cs x0 cs x1 x0 cs x0 cs'),
            B('x1 x0 cs x0 x1 x1 cs x1 x0 cs x0 cs')]
SQ_RULES = ['XSXS', 'CS4', 'I2', 'X11']
DE = {
  'H0': ([G('w'), G('K', 0, 1), G('K', 2, 3)], B('h0'),
         [B('w x1 ck x1 ck'), B('w w w w w w w w h0'), B('h0')], ['KK0', 'W8']),
  'H1': ([G('w'), G('K', 0, 2), G('K', 1, 3)], B('h1'),
         [B('w t1 x1 ck x1 t1 t1 ck t1'), B('w t1 x1 ck x1 ck t1'), B('w w w w w w w w t1 h0 t1'),
          B('t1 h0 t1'), B('h1')], ['KK0', 'P11', 'W8', 'T1H0']),
  'S0': ([G('i', 1), G('i', 3)], B('s0'), [B('x1 cs x1 cs'), B('s0 cs cs cs cs'), B('s0')], ['I1', 'CS4']),
  'S1': ([G('i', 2), G('i', 3)], B('s1'), [B('x0 cs x0 cs'), B('s1 cs cs cs cs'), B('s1')], ['I2', 'CS4']),
}

def std_certs():
    out = {}
    for f, (l0, r0, lines, names) in STD.items():
        L0, R0 = DBs(l0), DBs(r0)
        if lines is None: lines = [L0, R0]
        assert tuple(lines[0]) == tuple(L0) and tuple(lines[-1]) == tuple(R0), (f, lines[0], L0, lines[-1], R0)
        assert np.allclose(K.mat(L0), K.mat(R0)), f
        out[f] = thru(lines, names)
        assert run(L0, out[f]) == tuple(R0)
    sq = thru(SQ_LINES, SQ_RULES)
    rhs = DBs([G('i', 0), G('i', 1), G('i', 2), G('i', 3)])
    assert tuple(SQ_LINES[-1]) == tuple(rhs)
    out['sq'] = sq
    for g, (gs, tgt, lines, names) in DE.items():
        assert tuple(lines[0]) == tuple(DBs(gs)) and tuple(lines[-1]) == tuple(tgt), g
        out['DE ' + g] = thru(lines, names)
    return out

if __name__ == '__main__':
    sc = std_certs()
    for k, v in sc.items(): print(k, len(v))
