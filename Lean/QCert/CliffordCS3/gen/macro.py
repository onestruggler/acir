"""The macro alphabet for U_n(Z[1/2,i]), n = 4 or 8.

Tokens t_d (d < n - 1) are the transpositions (g[d] g[d+1]) of consecutive points of a Gray
path g (consecutive basis states differ in one bit); the atoms are Z = i_[z] and
K = K_[a, z] with (a, z) = (g[-2], g[-1]), a < z.  For every ordered pair of distinct points
(p, q) the macro word E(p, q) = v K v^-1 with v(a) = p, v(z) = q (v a fixed shortest token
word), F(p) = v Z v^-1 with v(z) = p, and X(p, q) = the canonical token word of the
transposition (p q).  The encodings: enc(K_[p,q]) = E(p,q), enc(i_[p]) = F(p),
enc(X_[p,q]) = X(p,q).

Macro words are lists of letters ('t', d), 'Z', 'K'.  Token words act on points with the
last letter first (matrix order)."""
from collections import deque
import itertools
import numpy as np
from qc import un_mat, perm_matrix, eq


class Macro:
    def __init__(self, n, gray, frames=None):
        self.frames = frames or {}
        self.n = n
        self.gray = list(gray)
        self.nt = n - 1
        for d in range(self.nt):
            x = gray[d] ^ gray[d + 1]
            assert x and (x & (x - 1)) == 0, 'not a Gray path'
        self.z = gray[-1]
        self.a = gray[-2]
        assert self.a < self.z
        self._bfs()
        self.mm = self.macro_mats()

    # ---------------------------------------------------------------- permutations
    def tperm(self, d):
        p = list(range(self.n))
        x, y = self.gray[d], self.gray[d + 1]
        p[x], p[y] = y, x
        return tuple(p)

    def perm_of(self, w):
        """The permutation of a token word (matrix order: the last letter acts first)."""
        p = tuple(range(self.n))
        for g in reversed(w):
            q = self.tperm(g[1])
            p = tuple(q[x] for x in p)
        return p

    def _bfs(self):
        n = self.n
        start = tuple(range(n))
        self.word = {start: ()}
        dq = deque([start])
        while dq:
            p = dq.popleft()
            for d in range(self.nt):
                q = self.tperm(d)
                p2 = tuple(q[x] for x in p)
                if p2 not in self.word:
                    self.word[p2] = (('t', d),) + self.word[p]
                    dq.append(p2)

    def frame(self, cond):
        best = None
        for p, w in self.word.items():
            if all(p[s] == t for s, t in cond) and (best is None or len(w) < len(best)):
                best = w
        return list(best)

    def vE(self, p, q):
        if (p, q) in self.frames:
            v = self.frames[(p, q)]
            pm = self.perm_of(v)
            assert pm[self.a] == p and pm[self.z] == q
            return list(v)
        return self.frame([(self.a, p), (self.z, q)])

    def vF(self, p):
        if p in self.frames:
            v = self.frames[p]
            assert self.perm_of(v)[self.z] == p
            return list(v)
        return self.frame([(self.z, p)])

    def wX(self, p, q):
        if getattr(self, 'xwords', None):
            return list(self.xwords[(p, q)])
        pm = list(range(self.n))
        pm[p], pm[q] = q, p
        return list(self.word[tuple(pm)])

    def E(self, p, q):
        v = self.vE(p, q)
        return v + ['K'] + list(reversed(v))

    def F(self, p):
        v = self.vF(p)
        return v + ['Z'] + list(reversed(v))

    def enc(self, g):
        if g[0] == 'X':
            return self.wX(g[1], g[2])
        if g[0] == 'i':
            return self.F(g[1])
        return self.E(g[1], g[2])

    def enc_word(self, w):
        out = []
        for g in w:
            out += self.enc(g)
        return out

    # ---------------------------------------------------------------- matrices
    def macro_mats(self):
        mm = {}
        for d in range(self.nt):
            mm[('t', d)] = perm_matrix(self.tperm(d))
        mm['Z'] = un_mat(self.n, ('i', self.z))
        mm['K'] = un_mat(self.n, ('K', self.a, self.z))
        return mm

    def mmat(self, w):
        r = np.eye(self.n, dtype=complex)
        for g in w:
            r = r @ self.mm[g]
        return r


def check(M):
    n = M.n
    gens = [('i', j) for j in range(n)] + [(t, j, k) for t in 'XK' for j in range(n) for k in range(j + 1, n)]
    for g in gens:
        assert eq(M.mmat(M.enc(g)), un_mat(n, g)), g
    return max(len(M.enc(g)) for g in gens)


if __name__ == '__main__':
    M4 = Macro(4, [1, 0, 2, 3])
    print('n=4 max enc', check(M4))
    M8 = Macro(8, [5, 1, 0, 4, 6, 2, 3, 7])
    print('n=8 max enc', check(M8))


def macro_axioms(M, std):
    """Macro axioms as (name, lhs, rhs) over macro letters: the Coxeter relations, the atoms
    commuting with the tokens of their stabilisers, and one standard instance of each family
    that needs one (`std`: family -> index tuple)."""
    t = lambda d: ('t', d)
    ax = []
    nt = M.nt
    for d in range(nt):
        ax.append(('sq%d' % d, [t(d), t(d)], []))
    for d in range(nt - 1):
        ax.append(('br%d' % d, [t(d), t(d + 1), t(d)], [t(d + 1), t(d), t(d + 1)]))
    for d in range(nt):
        for e in range(d + 2, nt):
            ax.append(('cm%d_%d' % (d, e), [t(d), t(e)], [t(e), t(d)]))
    for d in range(nt):
        p = M.tperm(d)
        if p[M.z] == M.z:
            ax.append(('Zc%d' % d, ['Z', t(d)], [t(d), 'Z']))
        if p[M.z] == M.z and p[M.a] == M.a:
            ax.append(('Kc%d' % d, ['K', t(d)], [t(d), 'K']))
    for fam, (l, r) in std_instances(std).items():
        ax.append((fam, M.enc_word(l), M.enc_word(r)))
    return ax


def std_instances(s):
    out = {}
    if 'r1' in s:
        z = s['r1']
        out['r1'] = ([('i', z)] * 4, [])
    if 'r3' in s:
        j, k = s['r3']
        out['r3'] = ([('K', j, k)] * 8, [])
    if 'r4' in s:
        a, b = s['r4']
        out['r4'] = ([('i', a), ('i', b)], [('i', b), ('i', a)])
    if 'r6' in s:
        a, j, k = s['r6']
        out['r6'] = ([('i', a), ('K', j, k)], [('K', j, k), ('i', a)])
    if 'r9' in s:
        j, k, l, m = s['r9']
        out['r9'] = ([('K', j, k), ('K', l, m)], [('K', l, m), ('K', j, k)])
    if 'r15' in s:
        j, k = s['r15']
        out['r15'] = ([('K', j, k), ('i', k), ('i', k)], [('X', j, k), ('K', j, k)])
        out['r16'] = ([('K', j, k)] + [('i', k)] * 3, [('i', k), ('K', j, k), ('i', k), ('K', j, k)])
        out['r17'] = ([('K', j, k), ('i', j), ('i', k)], [('i', j), ('i', k), ('K', j, k)])
        out['r18'] = ([('K', j, k), ('K', j, k), ('i', j), ('i', k)], [])
    if 'r19' in s:
        j, k, l, m = s['r19']
        out['r19'] = ([('K', j, k), ('K', l, m), ('K', j, l), ('K', k, m)],
                      [('K', j, l), ('K', k, m), ('K', j, k), ('K', l, m)])
    return out
