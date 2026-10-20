#!/usr/bin/env python3
"""The canonical K relations decoded through a pivot, and the V_Z finder.

Fix the pivot quadruple P = (12, 13, 14, 15), the plane x2 = x3 = 1.
Then K_A = (K_A K_P) K_P, and the edge (c, K_A) = rep(c) K_A rep(cK)⁻¹ is

    σ_c · Q_A · σ_c⁻¹ · E_c,

with Q_A = K_A K_P a K pair, σ_c = rep(c) z_c an even signed permutation
(z_c on the levels 10, 11, outside every canonical quadruple, fixing
the parity) acting on Q_A as rep(c) does, and E_c = rep(c) K_P rep(cK)⁻¹
the pivot edge.  Q_A is ρ_A q ρ_A⁻¹ for the canonical pair
q = K_(8,9,10,11) K_P, HH on the wires 0 1 under a black control on
wire 3 (the controlled-HH gadget), and ρ_A an even permutation fixing P
and sending 8, 9, 10, 11 to A in order.  E_c is decoded once (by
g4dec.py) for the states 00 and 10, and E_(cK) is its reverse, so two
consecutive K-edges multiply to Q_A Q_B⁻¹ up to the conjugation of a K
pair by a pivot edge.

    python3 -B g4dec2.py [family ...] [--limit L] [--max K] [--states S]
"""
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))
import g4vz as G
import g4dec as GDec
import canon4 as C4
import canonA16 as CA
import gadgets as GD

D = 16
P = (12, 13, 14, 15)
A0 = (8, 9, 10, 11)


class PivotDecoder:
    def __init__(self, V):
        self.V, self.A = V, V.A
        A = self.A
        self.q = tuple(GDec.placed(A, k, i, {0: 3, 1: 0, 2: 1, 3: 2}) for k, i in GD.CHHa)
        assert A.matrix(self.q) == GDec.src_matrix([('K', A0), ('K', P)]), 'q'
        old = GDec.Decoder(V)
        self.E = {}
        for c in ((0, 0), (1, 0)):
            c2, w = old.edge(c, ('K', P))
            self.E[c] = w
            self.E[c2] = tuple(reversed(w))
        self.z = {(0, 0): (), (1, 0): (('M', (10,)),), (1, 1): (('X', (10, 11)),),
                  (0, 1): (('M', (10,)), ('X', (10, 11)))}

    def rho(self, A_):
        """An even permutation fixing P, sending A0 to A_ in order."""
        assert not set(A_) & set(P), A_
        r = [-1] * D
        for x in P:
            r[x] = x
        for a, b in zip(A0, A_):
            r[a] = b
        src = [i for i in range(D) if r[i] == -1]
        tgt = [v for v in range(D) if v not in r]
        for i, v in zip(src, tgt):
            r[i] = v
        if sum(r[i] > r[j] for i in range(D) for j in range(i + 1, D)) % 2:
            i, k = src[:2]
            r[i], r[k] = r[k], r[i]
        return tuple(r)

    def edge(self, c, g):
        c2 = C4.step(c, g)
        right = tuple(reversed(C4.REPS[c2]))
        if g[0] in ('M', 'X'):
            M = GDec.src_matrix(C4.REPS[c] + (g,) + right)
            return c2, self.vzw(M)
        A_ = g[1]
        sigma = C4.REPS[c] + self.z[c]
        rho = self.rho(A_)
        rhow = GDec.perm_letters(rho)
        left = self.vzw(GDec.src_matrix(sigma + tuple(rhow)))
        rightw = self.vzw(GDec.src_matrix(tuple(reversed(rhow)) + tuple(reversed(sigma))))
        word = left + self.q + rightw + self.E[c]
        assert self.A.matrix(word) == GDec.src_matrix(C4.REPS[c] + (g,) + right), ('K-edge', c, g)
        return c2, word

    def vzw(self, M):
        p, d = [0] * D, [1] * D
        for i, (s, w) in enumerate(M):
            assert s == 0
            y = next(y for y in range(D) if w[y])
            p[i] = y
            d[y] = w[y]
        lab = self.V.canon_label(tuple(d), tuple(p))
        return tuple(g for m in lab for g in self.V.macros[m])

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
    mx = int(args[args.index('--max') + 1]) if '--max' in args else 2
    ns = int(args[args.index('--states') + 1]) if '--states' in args else 1
    fams = [a for a in args if a.startswith('r')] or ['r2f', 'r4b', 'r5a', 'r6a']
    V = G.VZFinder()
    Dc = PivotDecoder(V)
    print(len(V.A.rels), 'relators; q has', len(Dc.q), 'letters; pivot edges',
          [len(w) for w in Dc.E.values()], flush=True)
    for con in C4.TB.T1:
        if con[0] not in fams:
            continue
        for pat in C4.patterns(con)[:mx]:
            v = C4.instance(con, pat)
            for c in C4.STATES[:ns]:
                w = Dc.relation(con, v, c)
                assert V.A.is_identity(w)
                t0 = time.time()
                r = V.derive(w, limit)
                print(f'{con[0]} {pat} state {c}: {len(w)} letters, '
                      f'{"derived" if r else "NOT derived"} {round(time.time() - t0, 1)} s', flush=True)


if __name__ == '__main__':
    main()
