"""The local facts of the generic step, derived on three wires.

Every fact reads  lhs = k ; rhs  (time order) with k a K-word (K1 for stage
1, K2 for stage 2; names as in lib3.KL), and is derived by the width-3
engine from (C15)-(C18), the lemmas of lib3 and free two-wire segments.
Families (p0, p1 points of one wire, i in F3, x in {H0, S0}):

  S1a(p0,x)    alpha(p0) x            = k ; alpha(x.p0)            (p0 != 0)
  S1b(p0,x)    Gamma(p0) x            = k ; Gamma(x.p0)
  S1c(p0,c)    Gamma(p0) c            = k ; Gamma(p0)      c in S1, X1, Z1
  S1d(p0)      Gamma(p0) C1           = k ; Gamma(p0)
  S1e(p0)      alpha(p0) W0           = k ; W0 alpha'(p0)          (p0 != 0)
  S1f(p0,p1)   Gamma(p0) alpha'(p1) W0 = k ; sigma2(p1, p0)        (p1 != 0)
  S1g(p0,p1)   Gamma(p0) Gamma'(p1) W0 = k ; Gamma(p1) Gamma'(p0)
  S1h          C0 = W1 W0 C1 W0 W1
  S2a(i,s)     Q(i) s                 = k ; Q(s.i)         s in S0, X0, Z0
  S2b(i,s)     Q(i) C0 s              = k ; Q(s.i) C0
  S2c(c)       C0 c                   = k ; C0             c in S1, X1, Z1
  S2d          C0 C1                  = C1 ; C0
  S2e(i,t)     Q(i) t                 = k ; Q(i)           t in X0, Z0
  S2f(i,q1)    Q(i) C0 alpha'(q1) C0  = k ; tau2(i', q1')            (q1 != 0)
  S2g(i,q1)    Q(i) C0 Gamma'(q1) C0  = k ; Q(i') C0 Gamma'(q1')

(primes: one wire up; sigma2(p1, p0) = alpha(p1) if p0 = 0, else
Gamma(p1) alpha'(p0); tau2(i, q) = Q(i) if q = 0, else Q(i) C0 alpha'(q);
i' = i + q1.a, q1' = (q1.a, q1.b + 1)).
"""
import cliff
import qc
import sections as sec
from lib3 import *

K1N = ['S0', 'X0', 'Z0', 'C0', 'H1', 'S1']
K2N = ['X0', 'Z0', 'H1', 'S1']
PTS = [(a_, b_) for a_ in range(3) for b_ in range(3)]
NZ = [p for p in PTS if p != (0, 0)]


def al(p, j=0):
    return sec.alpha(p[0], p[1], j)


def Ga(p, j=0):
    return sec.Gamma(p[0], p[1], j)


def act1(g, p):
    P = qc.act([(g[0], 0)], (0, (p[0],), (p[1],)))
    return (P[1][0], P[2][0])


class Facts:
    def __init__(self):
        self.E = build()
        self.facts = []      # (family, params, lhs, k, rhs)

    def add(self, fam, params, lhs, k, rhs, chain=None):
        name = '%s%s' % (fam, params)
        target = evalK(k) + rhs
        if chain is None:
            chain = [lhs, target]
        self.E.chain(name, chain, rhs=target)
        self.facts.append((fam, params, lhs, k, rhs))

    def local(self, fam, params, lhs, rhs, names):
        k = kword(lhs + cliff.inv(rhs), names)
        self.add(fam, params, lhs, k, rhs)

    def stage1(self):
        for p in NZ:
            for g in (H0, S0):
                self.local('S1a', (p, g[0]), al(p) + [g], al(act1(g, p)), K1N)
        for p in PTS:
            for g in (H0, S0):
                self.local('S1b', (p, g[0]), Ga(p) + [g], Ga(act1(g, p)), K1N)
            for nm, c in (('S1', [S1]), ('X1', qc.X(1)), ('Z1', qc.Z(1))):
                self.local('S1c', (p, nm), Ga(p) + c, Ga(p), K1N)
        # S1d: CZ12 passes Gamma
        for p in PTS:
            if p == (0, 0):
                self.add('S1d', (p,), W0 + [C1], topword(W1) + ['C0'] + topword(W1), W0,
                         [W0 + [C1], W0 + [C1] + W0 + W0, D1 + W0])
            else:
                self.add('S1d', (p,), Ga(p) + [C1], ['C1'], Ga(p),
                         [Ga(p) + [C1], [H0] * 3 + [C0, C1, H0] + al(p),
                          [H0] * 3 + [C1, C0, H0] + al(p), [C1] + Ga(p)])
        for p in NZ:
            self.local('S1e', (p,), al(p) + W0, W0 + al(p, 1), K1N)
        for p0 in PTS:
            for p1 in NZ:
                rhs = al(p1) if p0 == (0, 0) else Ga(p1) + al(p0, 1)
                self.local('S1f', (p0, p1), Ga(p0) + al(p1, 1) + W0, rhs, K1N)
        for p0 in PTS:
            for p1 in PTS:
                self.s1g(p0, p1)
        self.add('S1h', (), [C0], [], W1 + W0 + [C1] + W0 + W1,
                 [[C0], [C0] + W1 + W1, [C0] + W1 + W0 + W0 + W1, W1 + W0 + [C1] + W0 + W1])

    def s1g(self, p0, p1):
        lhs = Ga(p0) + Ga(p1, 1) + W0
        rhs = Ga(p1) + Ga(p0, 1)
        if p0 != (0, 0) and p1 != (0, 0):
            k = self.E.B1k
            ch = [lhs, a + b + al(p0) + al(p1, 1) + W0, a + b + W0 + al(p1) + al(p0, 1),
                  evalK(k) + a + b + al(p1) + al(p0, 1)]
        elif p0 == (0, 0) and p1 != (0, 0):
            k = topword(W1)
            ch = [lhs, W0 + b + W0 + al(p1), W1 + a + W1 + al(p1)]
        elif p0 != (0, 0):
            k = topword(W1)
            ch = [lhs, a + W1 + al(p0) + W0, a + W1 + W0 + al(p0, 1), W1 + W0 + b + al(p0, 1)]
        else:
            k = topword(W1)
            ch = [lhs, W1 + W0 + W1]
        ch.append(evalK(k) + rhs)
        self.add('S1g', (p0, p1), lhs, k, rhs, ch)

    def stage2(self):
        def snext(s, i):
            P = qc.act(s, (0, (1,), (i,)))
            return P[2][0]
        sw = (('S0', [S0]), ('X0', qc.X(0)), ('Z0', qc.Z(0)))
        for i in range(3):
            for nm, s in sw:
                i2 = snext(s, i)
                self.local('S2a', (i, nm), sec.Q(i) + s, sec.Q(i2), K2N)
                self.local('S2b', (i, nm), sec.Q(i) + [C0] + s, sec.Q(i2) + [C0], K2N)
        for nm, c in (('S1', [S1]), ('X1', qc.X(1)), ('Z1', qc.Z(1))):
            self.local('S2c', (nm,), [C0] + c, [C0], K2N)
        self.add('S2d', (), [C0, C1], ['C1'], [C0])
        for i in range(3):
            for nm, t in (('X0', qc.X(0)), ('Z0', qc.Z(0))):
                self.local('S2e', (i, nm), sec.Q(i) + t, sec.Q(i), K2N)
        for i in range(3):
            for q in NZ:
                i2, q2 = (i + q[0]) % 3, (q[0], (q[1] + 1) % 3)
                rhs = sec.Q(i2) if q2 == (0, 0) else sec.Q(i2) + [C0] + al(q2, 1)
                self.local('S2f', (i, q), sec.Q(i) + [C0] + al(q, 1) + [C0], rhs, K2N)
        for i in range(3):
            for q in PTS:
                self.s2g(i, q)

    def zpow(self, w, i2):
        """c with Z0^c Q(i2) = w on wire 0."""
        for c in range(3):
            if cliff.key(qc.Z(0) * c + sec.Q(i2), 1) == cliff.key(w, 1):
                return c
        raise ValueError('no Z power')

    def s2g(self, i, q):
        i2, q2 = (i + q[0]) % 3, (q[0], (q[1] + 1) % 3)
        Q = sec.Q(i)
        lhs = Q + [C0] + Ga(q, 1) + [C0]
        rhs = sec.Q(i2) + [C0] + Ga(q2, 1)
        if q == (0, 0):
            y = W1 + x
            ch = [lhs, Q + W1 + W1 + [C0] + W1 + [C0], Q + W1 + D0 + [C0], Q + W1 + [C0] + D0,
                  Q + y + b + [C0] + D0, Q + y + [C0] + b]
            k = topword(y)
            ch.append(evalK(k) + rhs)
            self.add('S2g', (i, q), lhs, k, rhs, ch)
            return
        A = al(q, 1)
        ch = [lhs, Q + b + [C0] + D0 + A + [C0]]
        for j in range(1, len(A) + 1):
            ch.append(Q + b + [C0] + A[:j] + D0 + A[j:] + [C0])
        ch.append(Q + b + [C0] + A + [C0] + D0)
        e = [C0] + A + [C0]
        if q2 == (0, 0):
            # [C0] A [C0] is local
            d, u = oneword(e, 0), oneword(e, 1)
            ch.append(Q + b + d + u + D0)
            y = b + u + W1
            ch += [Q + d + b + u + D0, Q + d + y + W1 + D0, Q + d + y + W1 + D1,
                   Q + d + y + [C0] + W1]
            tail = [C0] + W1
        else:
            A2 = al(q2, 1)
            loc = e + cliff.inv([C0] + A2)
            d, u = oneword(loc, 0), oneword(loc, 1)
            y = b + u + x
            ch.append(Q + b + d + u + [C0] + A2 + D0)
            ch += [Q + d + b + u + [C0] + A2 + D0, Q + d + y + b + [C0] + A2 + D0]
            for j in range(len(A2) - 1, -1, -1):
                ch.append(Q + d + y + b + [C0] + A2[:j] + D0 + A2[j:])
            ch.append(Q + d + y + [C0] + b + A2)
            tail = [C0] + b + A2
        c = self.zpow(Q + d, i2)
        ch.append(qc.Z(0) * c + sec.Q(i2) + y + tail)
        k = ['Z0'] * c + topword(y)
        ch.append(evalK(k) + rhs)
        self.add('S2g', (i, q), lhs, k, rhs, ch)


def main():
    F = Facts()
    F.stage1()
    F.stage2()
    from collections import Counter
    cnt = Counter(f[0] for f in F.facts)
    print(dict(cnt), 'total', len(F.facts))
    print('lemmas', len(F.E.lemmas), 'table', len(F.E.table))
    return F


if __name__ == '__main__':
    main()
