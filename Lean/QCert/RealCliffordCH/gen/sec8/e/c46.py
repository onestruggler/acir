"""Rule (46), the core (147) with white controls: the paper's chain (pages 269-277)
as rewriting steps over gate descriptions (`E/Core46Kit.lean`).

`c46_chain.json` is the chain as read off the vector drawings of the paper (wires
0..3 explicit, the wires 4.. white throughout): 58 diagrams, every consecutive
pair semantically equal at N = 4, 5, 6.  Gates: ('g', K, tg, a) the
multi-controlled gate `mc N K tg (c4 a)` (a: colours of the wires 0..3, None
idle or special, the wires 4.. white); ('p', i, j) P (x) P on the wires i < j.

Facts: instances of canonical equations (Appendix D's (111), (112), (130),
(274), (277), (308), (309), (310), (311), (312), (335)-(345)) moved by a frame
(a permutation of the wires 0..3), each checked numerically.  Between two
consecutive diagrams the changed window is rewritten by a bidirectional search
over the facts.
"""
import sys, os, json, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
import numpy as np
import mc

T, F, Nn = True, False, None


def G(K, tg, a): return ('g', K, tuple(tg), tuple(a))
def P(i, j): return ('p', min(i, j), max(i, j))


def from_json(x):
    if x[0] == 'p': return P(x[1], x[2])
    return G(x[1], x[2], x[3])

# ---------------------------------------------------------------- semantics
_cache = {}


def gmat(g, N):
    key = (g, N)
    if key in _cache: return _cache[key]
    if g[0] == 'p':
        M = mc.mat(N, mc.ppAt(N, g[1], g[2]))
    else:
        _, K, tg, a = g
        d = {w: a[w] for w in range(4) if a[w] is not None and w not in tg}
        for w in range(4, N): d[w] = False
        M = mc.mc_sem(N, K, list(tg), mc.ctlDict(d))
    _cache[key] = M
    return M


def wmat(w, N):
    M = np.eye(2 ** N)
    for g in w: M = gmat(g, N) @ M
    return M


def sem_eq(l, r, Ns=(4, 5)):
    return all(np.allclose(wmat(l, N), wmat(r, N)) for N in Ns)

# ---------------------------------------------------------------- frames
PERMS = [list(p) for p in itertools.permutations(range(4))]


def fr(s, g):
    if g[0] == 'p': return P(s[g[1]], s[g[2]])
    _, K, tg, a = g
    a2 = [None] * 4
    for j in range(4): a2[s[j]] = a[j]
    return G(K, [s[t] for t in tg], a2)


def frl(s, l): return tuple(fr(s, g) for g in l)

# ---------------------------------------------------------------- canonical families
B2 = (T, F)


def canon():
    out = []  # (family, params, lhs, rhs)

    def add(fam, prm, l, r): out.append((fam, prm, tuple(l), tuple(r)))
    for x1, x2, x3 in itertools.product(B2, B2, B2):
        b = G('box', [0], [Nn, x1, x2, x3]); add('inv_box', (x1, x2, x3), [b, b], [])
    for x2, x3 in itertools.product(B2, B2):
        h = G('hg', [0, 1], [Nn, Nn, x2, x3]); add('inv_hg', (x2, x3), [h, h], [])
    add('inv_pp', (), [P(0, 1), P(0, 1)], [])
    for xs in itertools.product(B2, repeat=6):
        X = G('box', [0], [Nn, xs[0], xs[1], xs[2]]); Y = G('box', [0], [Nn, xs[3], xs[4], xs[5]])
        add('c335', xs, [X, Y], [Y, X])
    for c1, x2, x3, c2, y2, y3 in itertools.product(B2, repeat=6):
        X = G('box', [0], [Nn, c1, x2, x3]); Y = G('box', [1], [c2, Nn, y2, y3])
        add('c336', (c1, x2, x3, c2, y2, y3), [X, Y], [Y, X])
    for c1, x2, x3, y2, y3 in itertools.product(B2, repeat=5):
        X = G('box', [0], [Nn, c1, x2, x3])
        if (x2, x3) != (y2, y3):
            Y = G('hg', [0, 1], [Nn, Nn, y2, y3]); add('c337', (c1, x2, x3, y2, y3), [X, Y], [Y, X])
        Y = G('hg', [1, 0], [Nn, Nn, y2, y3]); add('c338', (c1, x2, x3, y2, y3), [X, Y], [Y, X])
    for c1, c2, x3, c3, y3 in itertools.product(B2, repeat=5):
        if x3 != y3:
            X = G('box', [0], [Nn, c2, c1, x3]); Y = G('hg', [1, 2], [c3, Nn, Nn, y3])
            add('c339', (c1, c2, x3, c3, y3), [X, Y], [Y, X])
    for c1, x3, c2, y3 in itertools.product(B2, repeat=4):
        if x3 != y3:
            X = G('hg', [0, 1], [Nn, Nn, c1, x3])
            Y = G('hg', [0, 2], [Nn, c2, Nn, y3]); add('c342', (c1, x3, c2, y3), [X, Y], [Y, X])
            Y = G('hg', [1, 2], [c2, Nn, Nn, y3]); add('c344', (c1, x3, c2, y3), [X, Y], [Y, X])
    for x2, x3, y2, y3 in itertools.product(B2, repeat=4):
        X = G('hg', [1, 0], [Nn, Nn, x2, x3]); Y = G('hg', [0, 1], [Nn, Nn, y2, y3])
        add('c345', (x2, x3, y2, y3), [X, Y], [Y, X])
        X = G('hg', [0, 1], [Nn, Nn, x2, x3])
        add('c340', (x2, x3, y2, y3), [X, Y], [Y, X])
    for x2, x3 in itertools.product(B2, B2):
        add('mv274', (x2, x3), [G('box', [0], [Nn, Nn, x2, x3])], [G('box', [1], [Nn, Nn, x2, x3])])
        add('d112', (x2, x3), [G('hg', [0, 1], [Nn, Nn, x2, x3])],
            [P(0, 1), G('box', [0], [Nn, T, x2, x3]), P(0, 1)])
        b = G('box', [1], [Nn, Nn, x2, x3]); add('c308', (x2, x3), [P(0, 1), b], [b, P(0, 1)])
    for x2 in B2:
        add('d112i', (x2,), [G('hg', [0, 1], [Nn, Nn, x2, Nn])], [P(0, 1), G('box', [0], [Nn, T, x2, Nn]), P(0, 1)])
    for x3 in B2:
        add('mv277', (x3,), [G('hg', [1, 2], [Nn, Nn, Nn, x3])], [G('hg', [0, 2], [Nn, Nn, Nn, x3])])
    add('klein1', (), [P(0, 1), P(0, 2)], [P(1, 2)])
    add('klein2', (), [P(0, 2), P(0, 1)], [P(1, 2)])
    return out


def merges():
    out = []
    OPT = (Nn, T, F)
    for t in range(4):
        for a in itertools.product(OPT, repeat=4):
            if a[t] is not None: continue
            for w in range(4):
                if w == t: continue
                for b in B2:
                    a1 = list(a); a1[w] = b; a2 = list(a); a2[w] = not b; a0 = list(a); a0[w] = Nn
                    out.append(('m309', (t, a, w, b), (G('box', [t], a1), G('box', [t], a2)),
                                (G('box', [t], a0),)))
    for bw, hw in itertools.permutations(range(4), 2):
        for a in itertools.product(OPT, repeat=4):
            if a[bw] is not None or a[hw] is not None: continue
            for w in range(4):
                if w in (bw, hw): continue
                for b in B2:
                    a1 = list(a); a1[w] = b; a2 = list(a); a2[w] = not b; a0 = list(a); a0[w] = Nn
                    out.append(('m310', (bw, hw, a, w, b), (G('hg', [bw, hw], a1), G('hg', [bw, hw], a2)),
                                (G('hg', [bw, hw], a0),)))
    return out


# preference: canonical position first, then frames in a fixed order
def all_facts():
    facts = {}
    for fam, prm, l, r in canon():
        for s in PERMS:
            L, R = frl(s, l), frl(s, r)
            key = (L, R)
            if key not in facts: facts[key] = (fam, prm, tuple(s))
    for fam, prm, l, r in merges():
        key = (l, r)
        if key not in facts: facts[key] = (fam, prm, None)
    return facts

# ---------------------------------------------------------------- search


REFS = {'311': ['inv_box'], '312': ['inv_hg'], '111': ['inv_pp'], '112': ['d112', 'd112i'],
        '130': ['klein1', 'klein2'], '308': ['c308'], '309': ['m309'], '310': ['m310'],
        '274': ['mv274'], '277': ['mv277'], '335': ['c335'], '336': ['c336'], '337': ['c337'],
        '338': ['c338'], '339': ['c339'], '342': ['c342'], '344': ['c344'], '345': ['c345'],
        '340': ['c340']}


def fams_of(refs):
    out = set()
    for r, fs in REFS.items():
        if r in refs: out |= set(fs)
    return out


def build_index(facts, allowed, fams, ins_ok):
    idx = {}
    for key, (fam, _, _) in facts.items():
        if fam not in fams: continue
        l, r = key
        if not all(g in allowed for g in l + r): continue
        for (a, b, fwd) in ((l, r, True), (r, l, False)):
            if not a and not all(g in ins_ok for g in b): continue
            k = a[0] if a else 'EMPTY'
            idx.setdefault(k, []).append((a, b, key, fwd))
    return idx


def neighbours(w, idx):
    for i in range(len(w)):
        for (a, b, key, fwd) in idx.get(w[i], []):
            if tuple(w[i:i + len(a)]) == a:
                yield (w[:i] + b + w[i + len(a):], (i, key, fwd))
    for i in range(len(w) + 1):
        for (a, b, key, fwd) in idx.get('EMPTY', []):
            yield (w[:i] + b + w[i:], (i, key, fwd))


def bisearch(A, B, idx, depth=10, maxw=40):
    if A == B: return []
    fa = {A: None}; fb = {B: None}
    qa = [A]; qb = [B]
    for d in range(depth):
        side_a = len(qa) <= len(qb)
        q, f, g = (qa, fa, fb) if side_a else (qb, fb, fa)
        nq = []
        for w in q:
            for (w2, st) in neighbours(w, idx):
                if len(w2) > maxw or w2 in f: continue
                f[w2] = (w, st)
                if w2 in g:
                    return join(fa, fb, w2)
                nq.append(w2)
        if side_a: qa = nq
        else: qb = nq
    return None


def join(fa, fb, m):
    left = []
    w = m
    while fa[w] is not None:
        p, st = fa[w]; left.append(st); w = p
    left.reverse()
    right = []
    w = m
    while fb[w] is not None:
        p, (i, key, fwd) = fb[w]
        right.append((i, key, not fwd)); w = p
    return left + right


def load_chain():
    data = json.load(open(os.path.join(HERE, 'c46_chain.json')))
    return [(d['name'], d['refs'], tuple(from_json(x) for x in d['word'])) for d in data]


def window(a, b):
    i = 0
    while i < min(len(a), len(b)) and a[i] == b[i]: i += 1
    j = 0
    while j < min(len(a), len(b)) - i and a[-1 - j] == b[-1 - j]: j += 1
    return i, a[i:len(a) - j], b[i:len(b) - j]


ALLPP = {P(i, j) for i in range(4) for j in range(i + 1, 4)}


def solve(facts, chain):
    """For each consecutive pair: (name, refs, offset, path) with path steps
    (i relative to the window, key, fwd)."""
    res = []
    for (n0, _, A), (n1, refs, B) in zip(chain, chain[1:]):
        if 'same' in refs:
            res.append((n1, refs, None, None)); continue
        off, wa, wb = window(A, B)
        fams = fams_of(refs)
        ins = {g for g in set(wa) | set(wb) if wa.count(g) != wb.count(g)}
        idx = build_index(facts, set(A) | set(B) | ALLPP, fams, ins)
        path = bisearch(wa, wb, idx)
        res.append((n1, refs, off, path))
    return res


