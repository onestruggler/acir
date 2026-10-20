#!/usr/bin/env python3
"""Distance two in the graph of lattices g·Z^16: the lattices h σ h Z^16
(σ in V_Z), classified by their relative position to Z^16, the 2-adic
elementary divisors of h σ h.

    python3 -B gz2.py [samples]"""
import sys
import random
from fractions import Fraction as F
from collections import Counter
import gz


def val2(x):
    """2-adic valuation of a nonzero Fraction"""
    n, d = x.numerator, x.denominator
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    while d % 2 == 0:
        d //= 2
        v -= 1
    return v


def elem_divisors(M):
    """2-adic valuations of the elementary divisors of a rational matrix"""
    A = [[F(x) for x in row] for row in M]
    n = len(A)
    out = []
    rows, cols = list(range(n)), list(range(n))
    for _ in range(n):
        best = None
        for i in rows:
            for j in cols:
                if A[i][j] != 0:
                    v = val2(A[i][j])
                    if best is None or v < best[0]:
                        best = (v, i, j)
        if best is None:
            break
        v, i, j = best
        out.append(v)
        piv = A[i][j]
        for r in rows:
            if r != i and A[r][j] != 0:
                f = A[r][j] / piv
                A[r] = [A[r][c] - f * A[i][c] for c in range(n)]
        for c in cols:
            if c != j and A[i][c] != 0:
                f = A[i][c] / piv
                for r in rows:
                    A[r][c] -= f * A[r][j]
        rows.remove(i)
        cols.remove(j)
    return tuple(sorted(out))


def hsh(p, s):
    M = gz.mul(gz.mul(gz.HM, gz.sp_mat(p, s)), gz.HM)
    return [[F(x, 4) for x in row] for row in M]


if __name__ == '__main__':
    random.seed(2)
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    gens = gz.vz_gens()
    seen = Counter()
    for _ in range(k):
        x = gz.random_vz(gens, 80)
        seen[elem_divisors(hsh(*x))] += 1
    for t, c in sorted(seen.items(), key=lambda t: -t[1]):
        print(c, t, flush=True)
