"""Labelled enumeration of the natural three-wire rules over W(D8) with
labels kept in a canonical form.

Labels are words in the W(D8) letters (labelled.py), but every join
replaces the label by the canonical word of its element: the sign part
(a word for the diagonal matrix) followed by the permutation part (the
BFS-first word in the classical letters).  The rewriting of a label to
its canonical word is recorded as one "normalisation" fact, to be
justified by the lower levels of the tower; here they are counted.

    python3 -B d8norm.py
"""
import sys, time, itertools
from collections import deque
sys.path.insert(0, '..')
import core as C
import natproof as NP
import labelled as LB
from d8tower import gs, w

LETTERS = ['X0', 'X1', 'X2', 'CX0', 'CX1', 'CCX0', 'CXr0', 'CXr1', 'Z1']
CLASSICAL = LETTERS[:-1]
MAC = {m: w(m) for m in LETTERS}

# Signed permutations of the 8 levels: a tuple t with t[i] = (j, s),
# the matrix sending e_i to s e_j.  A word g1 ... gk denotes G1 ... Gk.
ID = tuple((i, 1) for i in range(8))

def mat_of_gate(g):
    out = []
    for i in range(8):
        v = tuple(4 if k == i else 0 for k in range(8))
        u = gs.actions[g](v)
        nz = [(k, x) for k, x in enumerate(u) if x]
        if len(nz) != 1:
            return None
        k, x = nz[0]
        out.append((k, 1 if x > 0 else -1))
    return tuple(out)

def mul(a, b):
    # (A B) e_i = A (s e_j) = s A e_j
    out = []
    for i in range(8):
        j, s = b[i]
        k, t = a[j]
        out.append((k, s * t))
    return tuple(out)

def ev_letters(word_of_gates):
    """Signed permutation of a word of gates, None if not monomial."""
    m = ID
    # evaluate by acting on vectors, since HH alone is not monomial
    cols = []
    for i in range(8):
        v = tuple(4 if k == i else 0 for k in range(8))
        for g in reversed(word_of_gates):
            v = gs.actions[g](v)
        nz = [(k, x) for k, x in enumerate(v) if x]
        assert len(nz) == 1 and abs(nz[0][1]) == 4, (word_of_gates, v)
        k, x = nz[0]
        cols.append((k, 1 if x > 0 else -1))
    return tuple(cols)

EL = {m: ev_letters(MAC[m]) for m in LETTERS}

def ev(label):
    m = ID
    for x in label:
        m = mul(m, EL[x])
    return m

# BFS over S8 in the classical letters: canonical words for permutations.
def bfs_perm():
    start = ID
    best = {start: ()}
    q = deque([start])
    while q:
        p = q.popleft()
        for x in CLASSICAL:
            r = mul(p, EL[x])
            if r not in best:
                best[r] = best[p] + (x,)
                q.append(r)
    return best

PERM = bfs_perm()
assert len(PERM) == 40320, len(PERM)

# Words for diagonal sign matrices: Z_S for 4-sets S by conjugating Z1.
Z1 = EL['Z1']
Z1set = frozenset(i for i in range(8) if Z1[i][1] < 0)

def perm_part(m):
    return tuple((j, 1) for (j, s) in m)

def inv(m):
    out = [None] * 8
    for i, (j, s) in enumerate(m):
        out[j] = (i, s)
    return tuple(out)

ZS = {}
for p, word in PERM.items():
    # p Z1 p^-1 flips the image of Z1set under p
    S = frozenset(p[i][0] for i in Z1set)
    if S not in ZS or len(word) < len(ZS[S][0]):
        ZS[S] = (word, )
ZW = {}
for S, (word,) in ZS.items():
    ZW[S] = word + ('Z1',) + tuple(reversed(word))
assert len(ZW) == 70

def sign_word(T):
    T = frozenset(T)
    if not T:
        return ()
    if len(T) == 4:
        return ZW[T]
    if len(T) == 8:
        S = frozenset(range(4))
        return ZW[S] + ZW[frozenset(range(8)) - S]
    if len(T) == 2:
        a, b = sorted(T)
        rest = [i for i in range(8) if i not in T][:3]
        return ZW[frozenset([a] + rest)] + ZW[frozenset([b] + rest)]
    if len(T) == 6:
        return sign_word(frozenset(range(8)) - T) + sign_word(frozenset(range(8)))
    raise ValueError(T)

def canon(label):
    m = ev(label)
    P = perm_part(m)
    # m = D P with D diagonal: D = m P^-1
    D = mul(m, inv(P))
    T = [i for i in range(8) if D[i][1] < 0]
    word = sign_word(T) + PERM[P]
    assert ev(word) == m
    return word


class NormTC(LB.LabelledTC):
    def __init__(self, *a, **k):
        super().__init__(*a, **k)
        self.norms = 0

    def join(self, left, right):
        lab = tuple(left) + tuple(right)
        nf = canon(lab)
        if nf == lab:
            return lab, []
        self.norms += 1
        f = self._add(self.dec(lab), self.dec(nf), [(0, ("norm", (lab, nf)), True)])
        return nf, [(0, ("fact", f), True)]


if __name__ == '__main__':
    t0 = time.time()
    tc = NormTC(len(gs.names), NP.axioms(gs), MAC, limit=200_000)
    live = tc.run()
    print('live', len(live), 'defined', len(tc.rep), 'facts', len(tc.facts),
          'norm facts', tc.norms, 'time', round(time.time() - t0, 1), flush=True)
    sizes = []
    for c in live:
        for y in range(len(gs.names)):
            d, lab, f = tc.final(c, y)
            sizes.append(len(lab))
    print('label lengths: max', max(sizes), 'mean', round(sum(sizes) / len(sizes), 1))
    steps = [len(f.steps) for f in tc.facts]
    print('fact steps: max', max(steps), 'total', sum(steps))

def closure(tc, roots):
    seen, stack = set(), list(roots)
    while stack:
        f = stack.pop()
        if f in seen:
            continue
        seen.add(f)
        for (_, (kind, key), _) in tc.facts[f].steps:
            if kind == 'fact':
                stack.append(key)
    return seen

if __name__ == '__main__':
    roots = []
    for c in live:
        for y in range(len(gs.names)):
            roots.append(tc.final(c, y)[2])
    cl = closure(tc, roots)
    norm = sum(1 for f in cl if any(k == 'norm' for (_, (k, _), _) in tc.facts[f].steps))
    print('closure facts', len(cl), 'norm facts in closure', norm,
          'steps', sum(len(tc.facts[f].steps) for f in cl))
