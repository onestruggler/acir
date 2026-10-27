"""Linear normal form `sh h * fo c * R r` (Linear.lean): the eleven closure
cases of `R_mul_gen` and the pushes of the fans, checked at widths 2-5."""
import itertools
from sim import *

def vecs(n):
    return list(itertools.product((0, 1), repeat=n))

def F(m, cvec):          # width m = n+1, cvec in F2^n: fan-out from 0 to j+1
    return prod([c(m, 0, j + 1) for j, b in enumerate(cvec) if b], m)

def N(m, s):             # fan-in into 0 from j+1
    return prod([c(m, j + 1, 0) for j, b in enumerate(s) if b], m)

def R(m, r):             # r in F2^m, nonzero
    if r[0] == 1:
        return N(m, r[1:])
    return sw(m, 0) * shift(R(m - 1, r[1:]))

def row0(op):
    m = op.n
    return tuple(op.f[tuple(1 if k == j else 0 for k in range(m))][0] for j in range(m))

# generators of width m, as (kind, i)
def gens(m):
    return [('cx', i) for i in range(m - 1)] + [('sw', i) for i in range(m - 1)]

def gop(m, g):
    k, i = g
    return cx(m, i) if k == 'cx' else sw(m, i)

def rmul(r, g):
    """row vector r times matrix of g"""
    k, i = g
    r = list(r)
    if k == 'cx':      # c(i+1, i): x_i += x_{i+1}; matrix I + E_{i,i+1}; (rg)_{i+1} = r_{i+1} + r_i
        r[i + 1] ^= r[i]
    else:
        r[i], r[i + 1] = r[i + 1], r[i]
    return tuple(r)

def closure(m, r, g):
    """returns (h, d) with R(r) * g = sh(h) * F(d) * R(r g); h an op on m-1 wires"""
    n = m - 1
    k, i = g
    zero = tuple([0] * n)
    if i >= 1:
        gp = (k, i - 1)
        if r[0] == 1:
            return gop(n, gp), zero
        hp, dp = closure(n, r[1:], gp)
        # sh(sh(h')) * F((0, d')) ; h = sh(h')
        return shift(hp), (0,) + dp
    rest = r[2:]
    if r[0] == 1:
        if k == 'cx':
            return ident(n), zero
        if r[1] == 1:
            return N(n, rest), (1,) + tuple([0] * (n - 1))
        return ident(n), zero
    else:
        if k == 'cx':
            if r[1] == 1:
                return N(n, rest), (1,) + tuple([0] * (n - 1))
            return cx(n, 0), zero
        if r[1] == 0:
            return sw(n, 0), zero
        return ident(n), zero

def check(m):
    n = m - 1
    bad = 0
    for r in vecs(m):
        if not any(r):
            continue
        assert row0(R(m, r)) == r, (r, row0(R(m, r)))
        for g in gens(m):
            h, d = closure(m, r, g)
            lhs = R(m, r) * gop(m, g)
            rhs = shift(h) * F(m, d) * R(m, rmul(r, g))
            if lhs != rhs:
                bad += 1
                print('FAIL', m, r, g)
    print('width', m, 'closure failures', bad)

for m in range(2, 6):
    check(m)

# F-push and N-push for upper generators
def fpush(m):
    n = m - 1
    for cv in vecs(n):
        for g in gens(n):
            gp = gop(n, g)
            # F(c) * sh(g) = sh(g) * F(g^{-1} c)
            cnew = tuple(gp.inv().f[cv]) if n > 0 else cv
            assert F(m, cv) * shift(gp) == shift(gp) * F(m, cnew)
            # N(s) * sh(g) = sh(g) * N(s g)
            snew = rmul(cv, g)
            assert N(m, cv) * shift(gp) == shift(gp) * N(m, snew)
    print('push ok', m)

for m in range(2, 6):
    fpush(m)
