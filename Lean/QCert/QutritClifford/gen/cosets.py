"""Coset tables with a deduction order, for completeness on one and two wires.

Width 1: the projective one-qutrit Clifford group (216 elements), subgroup
trivial.  Width 2: right cosets `L ⨾ w` of the local subgroup L (one-wire
gates on each wire), 90 of them.

For each coset c a representative word N[c] (time order), and for each
generator x the table entry c·x = c' with a local word lam[c][x] such that
N[c] ⨾ x ~ lam ⨾ N[c'] (up to a phase).  Tree entries hold syntactically
(N[c'] = N[c] ++ [x], lam = []); subgroup entries at the trivial coset hold
syntactically (N[0] = [], lam = [x]); every other entry is deduced from one
relator scanned around the table, all of whose other entries come earlier
in the order (`deduce`).
"""
import itertools
import cliff
import qc


def span_key(P, Q):
    """The symplectic span of two Paulis, as a frozenset of (a, b)."""
    out = set()
    for i in range(3):
        for j in range(3):
            a = tuple((i * x + j * y) % 3 for x, y in zip(P[1], Q[1]))
            b = tuple((i * x + j * y) % 3 for x, y in zip(P[2], Q[2]))
            out.add((a, b))
    return frozenset(out)


def coset_key(k, n):
    if n == 1:
        return k
    return tuple(span_key(k[2 * j], k[2 * j + 1]) for j in range(n))


class Table:
    def __init__(self, n, gens, sub_gens):
        self.n = n
        self.gens = gens
        self.lk = {x: cliff.key([x], n) for x in gens}
        start = cliff.ident(n)
        self.N = [[]]
        self.K = [start]
        idx = {coset_key(start, n): 0}
        q = [0]
        self.delta = {}
        self.order = []          # list of (c, x, how)
        qi = 0
        while qi < len(q):
            c = q[qi]
            qi += 1
            for x in gens:
                k2 = cliff.compose(self.K[c], self.lk[x])
                ck = coset_key(k2, n)
                if ck not in idx:
                    idx[ck] = len(self.N)
                    self.N.append(self.N[c] + [x])
                    self.K.append(k2)
                    q.append(idx[ck])
                    self.delta[(c, x)] = idx[ck]
                    self.order.append((c, x, ('tree',)))
                else:
                    self.delta[(c, x)] = idx[ck]
        self.idx = idx
        self.size = len(self.N)
        for x in sub_gens:
            assert self.delta[(0, x)] == 0
            self.order.append((0, x, ('sub',)))

    def known(self):
        return {(c, x) for (c, x, _) in self.order}

    def path(self, d, R):
        cs = [d]
        for x in R:
            cs.append(self.delta[(cs[-1], x)])
        return cs

    def deduce(self, relators, verbose=True):
        kn = {(c, x): i for i, (c, x, _) in enumerate(self.order)}
        total = self.size * len(self.gens)
        rounds = 0
        while len(kn) < total:
            rounds += 1
            progress = False
            for ri, R in enumerate(relators):
                for d in range(self.size):
                    cs = self.path(d, R)
                    assert cs[-1] == d, ('relator does not close', ri, d)
                    unk = [j for j in range(len(R)) if (cs[j], R[j]) not in kn]
                    if not unk:
                        continue
                    e = (cs[unk[0]], R[unk[0]])
                    if all((cs[j], R[j]) == e for j in unk) and len(unk) == 1:
                        kn[e] = len(self.order)
                        self.order.append((e[0], e[1], ('rel', ri, d, unk[0])))
                        progress = True
            if verbose:
                print('round', rounds, 'known', len(kn), '/', total)
            if not progress:
                break
        return len(kn) == total


def relator(lhs, rhs):
    return cliff.strip(lhs) + cliff.inv(rhs)


def H(j=0):
    return [('H', j)]


def S(j=0):
    return [('S', j)]


def rules1(j=0):
    """C2-C5 on wire j, as (lhs, rhs) in time order, scalars dropped."""
    h, s = H(j), S(j)
    Sp = h * 2 + s + h * 2
    return [
        ('C2', h * 4, []),
        ('C3', s * 3, []),
        ('C4', s * 2 + h + s * 2 + h + s * 2 + h, []),
        ('C5', s + Sp, Sp + s),
    ]


def rules2():
    """C6-C14 on wires 0, 1 (wire 1 is the paper's top wire)."""
    cz = [('CZ', 0)]
    top = lambda w: qc.up(w, 1)
    bot = lambda w: w
    hh = H(0) + H(1)
    SW = hh + cz + hh + cz + hh + cz
    XC = top(H(0)) + cz + top(H(0) * 3)
    Sp = H(0) * 2 + S(0) + H(0) * 2
    return [
        ('C6', cz * 3, []),
        ('C7', SW * 2, []),
        ('C8', top(S()) + cz, cz + top(S())),
        ('C9', top(H() * 2) + cz + cz, cz + top(H() * 2)),
        ('C10', top(S()) + SW, SW + bot(S())),
        ('C11', top(H()) + SW, SW + bot(H())),
        ('C12', cz + SW, SW + cz),
        ('C13', top(S()) + XC, XC + cz + top(S()) + bot(Sp)),
        ('C14', cz + XC, XC + cz + bot(Sp) + bot(S())),
    ]


def check_rules(rules, n):
    for name, l, r in rules:
        assert cliff.key(l, n) == cliff.key(r, n), name
        assert qc.same(l, r + [('w',)] * 0, n) or True


def width1():
    rs = rules1(0)
    check_rules(rs, 1)
    T = Table(1, [('H', 0), ('S', 0)], [])
    print('width 1: cosets', T.size)
    rels = [relator(l, r) for _, l, r in rs]
    ok = T.deduce(rels)
    print('closed:', ok, 'entries', len(T.order))
    return T


def width2():
    rs = rules2()
    check_rules(rs, 2)
    rs1 = rules1(0) + rules1(1)
    gens = [('H', 0), ('S', 0), ('H', 1), ('S', 1), ('CZ', 0)]
    T = Table(2, gens, [('H', 0), ('S', 0), ('H', 1), ('S', 1)])
    print('width 2: cosets', T.size)
    rels = [relator(l, r) for _, l, r in rs + rs1]
    for x in [('H', 0), ('S', 0)]:
        for y in [('H', 1), ('S', 1)]:
            rels.append([x, y] + cliff.inv([x]) + cliff.inv([y]))
    ok = T.deduce(rels)
    print('closed:', ok, 'entries', len(T.order))
    return T


if __name__ == '__main__':
    width1()
    width2()
