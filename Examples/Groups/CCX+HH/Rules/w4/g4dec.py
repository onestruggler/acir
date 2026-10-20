#!/usr/bin/env python3
"""The canonical K relations of Table 1 on four wires, decoded into
circuits, and the V_Z finder (`g4vz.py`) run on them.

An edge (state c, letter g) is rep(c) · g · rep(c·g)⁻¹.  An M- or
X-edge is a signed permutation, decoded as its canonical V_Z word.  A
K-edge L · K_A · R is T · S⁻¹ · J_A · S with T, S signed permutations
(as ../../../CCX+H/GeneralN/construct.py's k_factors) and J_A the mixed
atom M_a X_bc K_A; J_A is ρ J₀ ρ⁻¹ for an even permutation ρ sending
0, 1, 2, 3 to A in order, and the core J₀ = J_(0,1,2,3) is the circuit
q s q s, q = K_(0123) K_(4567) (HH on wires 0 1 under a white control on
wire 3, the controlled-HH gadget of NaturalP/Ctrl borrowing wire 2) and
s = M_0 M_8 (a CCZ under negated controls).

    python3 -B g4dec.py [family ...] [--limit L] [--max K] [--merge] [--lemmas]
"""
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))
import g4vz as G
import canon4 as C4
import canonA16 as CA
import gadgets as GD
from diag4 import mono_word

D = 16


def placed(A, kind, i, f):
    """The adjacent gate (kind, i) placed by the wire map f, as a letter."""
    if kind == 'X':
        return A.INDEX[('X', f[i])]
    if kind == 'CX':
        return A.INDEX[('CX', f[i + 1], f[i])]
    if kind == 'CCX':
        a, b = sorted((f[i + 1], f[i + 2]))
        return A.INDEX[('CCX', f[i], a, b)]
    a, b = sorted((f[i], f[i + 1]))
    return A.INDEX[(kind, a, b)]


# ---------------------------------------------------------------------
# source letters as column matrices (scale, entries), as finder.matrix

def act_src(g, col):
    s, w = col
    k, ix = g
    w = list(w)
    if k == 'M':
        w[ix[0]] = -w[ix[0]]
        return s, tuple(w)
    if k == 'X':
        a, b = ix
        w[a], w[b] = w[b], w[a]
        return s, tuple(w)
    # 2 K w: the block's sums and differences, every other entry doubled
    old = [w[r] for r in ix]
    w = [2 * x for x in w]
    for i, r in enumerate(ix):
        w[r] = sum((-1) ** bin(i & j).count('1') * old[j] for j in range(4))
    s += 2
    while s >= 2 and all(v % 2 == 0 for v in w):
        s -= 2
        w = [v // 2 for v in w]
    return s, tuple(w)


def src_matrix(word):
    cols = []
    for i in range(D):
        c = (0, tuple(1 if j == i else 0 for j in range(D)))
        for g in reversed(word):
            c = act_src(g, c)
        cols.append(c)
    return tuple(cols)


def perm_letters(p):
    """A source word (X letters) for the permutation p (p[x] = image)."""
    out, q = [], list(p)
    # sort by transpositions: build p from the identity
    cur = list(range(D))
    word = []
    pos = {v: i for i, v in enumerate(cur)}
    for x in range(D):
        if cur[x] != p[x]:
            y = pos[p[x]]
            word.append(('X', (min(x, y), max(x, y))))
            cur[x], cur[y] = cur[y], cur[x]
            pos[cur[x]], pos[cur[y]] = x, y
    return word


class Decoder:
    def __init__(self, V):
        self.V, self.A = V, V.A
        A = self.A
        f = {0: 3, 1: 0, 2: 1, 3: 2}
        chh = tuple(placed(A, k, i, f) for k, i in GD.CHHa)
        x3 = A.IX['X3']
        self.q = (x3,) + chh + (x3,)
        xs = tuple(A.IX[n] for n in ('X0', 'X1', 'X2'))
        self.s = xs + mono_word(A, (0, 1, 2)) + xs
        self.j = self.q + self.s + self.q + self.s
        K0123 = ('K', (0, 1, 2, 3))
        assert A.matrix(self.q) == src_matrix([K0123, ('K', (4, 5, 6, 7))]), 'q'
        assert A.matrix(self.s) == src_matrix([('M', (0,)), ('M', (8,))]), 's'
        assert A.matrix(self.j) == src_matrix([('M', (0,)), ('X', (1, 2)), K0123]), 'j'

    def vz_word(self, M):
        """The canonical V_Z circuit of a signed permutation matrix."""
        p, d = [0] * D, [1] * D
        for i, (s, w) in enumerate(M):
            assert s == 0
            y = next(y for y in range(D) if w[y])
            p[i] = y
            d[y] = w[y]
        lab = self.V.canon_label(tuple(d), tuple(p))
        return tuple(g for m in lab for g in self.V.macros[m])

    def edge(self, c, g):
        c2 = C4.step(c, g)
        right = tuple(reversed(C4.REPS[c2]))
        if g[0] in ('M', 'X'):
            return c2, self.vz_word(src_matrix(C4.REPS[c] + (g,) + right))
        A_ = g[1]
        a, b, cc, _ = A_
        left = C4.REPS[c]
        t = left + (('X', (b, cc)), ('M', (a,))) + right
        e, ff = [i for i in range(D) if i not in A_][:2]
        z = ((('M', (e,)),) if sum(x[0] == 'M' for x in right) % 2 else ())
        z += ((('X', (e, ff)),) if sum(x[0] == 'X' for x in right) % 2 else ())
        s = z + right
        # rho: an even permutation sending 0, 1, 2, 3 to A in order
        rho = [-1] * D
        for i, v in enumerate(A_):
            rho[i] = v
        free_src = [i for i in range(D) if rho[i] == -1]
        free_tgt = [v for v in range(D) if v not in A_]
        for i, v in zip(free_src, free_tgt):
            rho[i] = v
        par = sum(rho[i] > rho[j] for i in range(D) for j in range(i + 1, D)) % 2
        if par:
            i, k = free_src[:2]
            rho[i], rho[k] = rho[k], rho[i]
        P = perm_letters(rho)
        Pinv = list(reversed(P))
        T_Si_P = src_matrix(t + tuple(reversed(s)) + tuple(P))
        Pi_S = src_matrix(tuple(Pinv) + s)
        word = self.vz_word(T_Si_P) + self.j + self.vz_word(Pi_S)
        assert self.A.matrix(word) == src_matrix(C4.REPS[c] + (g,) + right), 'K-edge'
        return c2, word

    def relation(self, con, v, c):
        r = C4.relator(con, v)
        state, out = c, ()
        for g in r:
            state, w = self.edge(state, g)
            out += w
        assert state == c
        return out


def main():
    args = sys.argv[1:]
    limit = int(args[args.index('--limit') + 1]) if '--limit' in args else 30_000
    mx = int(args[args.index('--max') + 1]) if '--max' in args else 4
    fams = [a for a in args if a.startswith('r')] or ['r2f', 'r4b', 'r5a', 'r6a']
    extra = []
    if '--merge' in args:
        # the merge of a white- and a black-controlled HH, at every
        # placement of the gadget's wires
        import itertools
        import finder as F
        A0 = F.Alphabet(4)
        for perm in itertools.permutations(range(4)):
            f = {0: perm[3], 1: perm[0], 2: perm[1], 3: perm[2]}
            chh = tuple(placed(A0, k, i, f) for k, i in GD.CHHa)
            xc = A0.INDEX[('X', perm[3])]
            hh = A0.INDEX[('HH', min(perm[0], perm[1]), max(perm[0], perm[1]))]
            extra.append((xc,) + chh + (xc,) + chh + (hh,))
    if '--lemmas' in args:
        import lemmas4
        extra += lemmas4.load()
    V = G.VZFinder(extra=extra)
    Dc = Decoder(V)
    print(len(V.A.rels), 'relators; core j has', len(Dc.j), 'letters', flush=True)
    for con in C4.TB.T1:
        if con[0] not in fams:
            continue
        for n, pat in enumerate(C4.patterns(con)[:mx]):
            v = C4.instance(con, pat)
            for c in C4.STATES[:1]:
                w = Dc.relation(con, v, c)
                assert V.A.is_identity(w)
                t0 = time.time()
                r = V.derive(w, limit)
                print(f'{con[0]} pattern {pat} state {c}: {len(w)} letters, '
                      f'{"derived" if r else "NOT derived"} {round(time.time() - t0, 1)} s', flush=True)


if __name__ == '__main__':
    main()
