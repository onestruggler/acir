"""Coset certificates for completeness on one and two wires (Coset.lean).

Letters in time order; letter indices: width 1: H0, S0; width 2: H0, S0,
H1, S1, CZ.  For each coset c a representative rep[c] (rep[0] = []), the
table dl[c][x], and for each edge (c, x) an order index and a deduction:
  ('tree',)              rep[dl[c][x]] = rep[c] ++ [x]
  ('sub',)               c = 0, x local, dl[0][x] = 0
  ('eq', e, d, side, j)  equation e scanned from coset d; the edge is the
                         j-th edge of side l (side 0) or r (side 1), every
                         other edge of the scan coming earlier.
An equation is (l, r, at): l = r up to a local word on the left, at every
coset (at = None) or at the coset at only (a stabiliser fact
rep[at] ++ l = mu ++ rep[at], r = []).
"""
import cliff
import qc
import cosets

H0, S0, H1, S1, CZ = ('H', 0), ('S', 0), ('H', 1), ('S', 1), ('CZ', 0)


def rules1(j=0):
    return [(cliff.strip(l), cliff.strip(r)) for _, l, r in cosets.rules1(j)]


def rules2():
    return [(cliff.strip(l), cliff.strip(r)) for _, l, r in cosets.rules2()]


class Cert:
    def __init__(self, n, letters, sub, eqs):
        self.n, self.letters = n, letters
        self.T = cosets.Table(n, letters, sub)
        self.eqs = eqs
        T = self.T
        self.rep = T.N
        self.dl = [[T.delta[(c, x)] for x in letters] for c in range(T.size)]
        self.order = {}
        self.ded = {}
        for (c, x, how) in T.order:
            self.order[(c, letters.index(x))] = len(self.order)
            self.ded[(c, letters.index(x))] = how

    def walk(self, d, w):
        cs = [d]
        for x in w:
            cs.append(self.dl[cs[-1]][self.letters.index(x)])
        return cs

    def close(self, verbose=False):
        total = self.T.size * len(self.letters)
        while len(self.order) < total:
            prog = False
            for ei, (l, r, at) in enumerate(self.eqs):
                ds = range(self.T.size) if at is None else [at]
                for d in ds:
                    cl, cr = self.walk(d, l), self.walk(d, r)
                    assert cl[-1] == cr[-1], (ei, d)
                    edges = [(cl[j], self.letters.index(l[j]), 0, j) for j in range(len(l))] + \
                        [(cr[j], self.letters.index(r[j]), 1, j) for j in range(len(r))]
                    unk = [e for e in edges if (e[0], e[1]) not in self.order]
                    if len(unk) == 1:
                        c, xi, side, j = unk[0]
                        self.order[(c, xi)] = len(self.order)
                        self.ded[(c, xi)] = ('eq', ei, d, side, j)
                        prog = True
            if verbose:
                print('known', len(self.order), '/', total)
            if not prog:
                return False
        return True

    def check(self):
        """Every deduction scans with all other edges earlier."""
        for (c, xi), how in self.ded.items():
            o = self.order[(c, xi)]
            if how[0] == 'tree':
                assert self.rep[self.dl[c][xi]] == self.rep[c] + [self.letters[xi]]
            elif how[0] == 'sub':
                assert c == 0 and self.dl[0][xi] == 0
            else:
                _, ei, d, side, j = how
                l, r, at = self.eqs[ei]
                assert at is None or at == d
                cl, cr = self.walk(d, l), self.walk(d, r)
                assert cl[-1] == cr[-1]
                sw = (l, cl) if side == 0 else (r, cr)
                assert sw[1][j] == c and self.letters.index(sw[0][j]) == xi
                for (w, cs, s) in ((l, cl, 0), (r, cr, 1)):
                    for t in range(len(w)):
                        if (s, t) == (side, j):
                            continue
                        assert self.order[(cs[t], self.letters.index(w[t]))] < o

    def local_check(self):
        """No representative but rep[0] acts locally."""
        for c in range(1, self.T.size):
            k = cliff.key(self.rep[c], self.n)
            if self.n == 1:
                assert k != cliff.ident(1), c
                continue
            loc = all(k[2 * j][1][t] == 0 and k[2 * j][2][t] == 0 and
                      k[2 * j + 1][1][t] == 0 and k[2 * j + 1][2][t] == 0
                      for j in range(self.n) for t in range(self.n) if t != j)
            assert not loc, c


def width1():
    eqs = [(l, r, None) for (l, r) in rules1(0)]
    C = Cert(1, [H0, S0], [], eqs)
    assert C.close()
    C.check()
    C.local_check()
    return C


def width2(stab):
    """stab: list of (coset, m, mu) stabiliser facts."""
    eqs = [(l, r, None) for (l, r) in rules2()]
    eqs += [(l, r, None) for (l, r) in rules1(0)]
    eqs += [(qc.up(l, 1), qc.up(r, 1), None) for (l, r) in rules1(0)]
    for x in (H0, S0):
        for y in (H1, S1):
            eqs.append(([x, y], [y, x], None))
    for (c, m, mu) in stab:
        eqs.append((m, [], c))
    C = Cert(2, [H0, S0, H1, S1, CZ], [H0, S0, H1, S1], eqs)
    assert C.close(), 'width 2 does not close'
    C.check()
    C.local_check()
    return C


if __name__ == '__main__':
    C1 = width1()
    print('width 1:', C1.T.size, 'cosets,', len(C1.order), 'edges')
    import facts2
    E, Pa, out = facts2.build_stab()
    facts2.d27_facts(E, Pa, out)
    stab = [(c, m, mu) for c, v in out.items() for (m, mu) in v]
    C2 = width2(stab)
    print('width 2:', C2.T.size, 'cosets,', len(C2.order), 'edges')
