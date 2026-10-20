#!/usr/bin/env python3
"""The graph of lattices g·Z^16 on four wires: vertex group V_Z (the
signed permutations in the circuit group), step h = HH(0,1).

    python3 -B gz.py

A signed permutation is (p, s): e_i -> s[i] e_{p[i]}.  V_Z is the even
signed permutations with an even permutation (the classical gates and
the sign gates generate it).  h is K = H (x) H on each of the four
blocks {x : (x2, x3) fixed}.  E_h = V_Z ∩ h V_Z h is the stabiliser of
h·Z^16 in V_Z; the neighbours of Z^16 number |V_Z| / |E_h|."""
import random
from math import factorial
import ss

N = 16
H4 = [[1, 1, 1, 1], [1, -1, 1, -1], [1, 1, -1, -1], [1, -1, -1, 1]]


def blocks():
    out = []
    for b in range(4):
        out.append([b << 2 | j for j in range(4)])
    return out


BLK = blocks()


def sp_mat(p, s):
    M = [[0] * N for _ in range(N)]
    for i in range(N):
        M[p[i]][i] = s[i]
    return M


def h_mat():
    M = [[0] * N for _ in range(N)]   # scaled by 2
    for b in BLK:
        for r in range(4):
            for c in range(4):
                M[b[r]][b[c]] = H4[r][c]
    return M


def mul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(N)) for j in range(N)] for i in range(N)]


HM = h_mat()


def conj_is_sp(p, s):
    """h σ h is a signed permutation?  (h σ h) = HM σ HM / 4."""
    M = mul(mul(HM, sp_mat(p, s)), HM)
    for row in M:
        nz = [x for x in row if x]
        if len(nz) != 1 or abs(nz[0]) != 4:
            return False
    return True


def to_perm32(p, s):
    """as a permutation of the 32 points ±e_i (point 2i is +e_i, 2i+1 is -e_i)"""
    out = [0] * 32
    for i in range(N):
        j = p[i]
        if s[i] == 1:
            out[2 * i], out[2 * i + 1] = 2 * j, 2 * j + 1
        else:
            out[2 * i], out[2 * i + 1] = 2 * j + 1, 2 * j
    return tuple(out)


def gate_sp(kind, wires):
    def bit(x, k):
        return x >> k & 1
    p = list(range(N))
    s = [1] * N
    if kind == 'X':
        t, = wires
        p = [x ^ (1 << t) for x in range(N)]
    elif kind == 'CX':
        c, t = wires
        p = [x ^ (1 << t) if bit(x, c) else x for x in range(N)]
    elif kind == 'CCX':
        c1, c2, t = wires
        p = [x ^ (1 << t) if bit(x, c1) and bit(x, c2) else x for x in range(N)]
    elif kind == 'Z':
        t, = wires
        s = [-1 if bit(x, t) else 1 for x in range(N)]
    elif kind == 'CZ':
        a, b = wires
        s = [-1 if bit(x, a) and bit(x, b) else 1 for x in range(N)]
    elif kind == 'CCZ':
        a, b, c = wires
        s = [-1 if bit(x, a) and bit(x, b) and bit(x, c) else 1 for x in range(N)]
    return p, s


def vz_gens():
    g = []
    for i in range(4):
        g.append(gate_sp('X', (i,)))
        g.append(gate_sp('Z', (i,)))
    for c in range(4):
        for t in range(4):
            if c != t:
                g.append(gate_sp('CX', (c, t)))
    for a in range(4):
        for b in range(a + 1, 4):
            g.append(gate_sp('CZ', (a, b)))
    import itertools
    for t in range(4):
        for c1, c2 in itertools.combinations([x for x in range(4) if x != t], 2):
            g.append(gate_sp('CCX', (c1, c2, t)))
    for a, b, c in itertools.combinations(range(4), 3):
        g.append(gate_sp('CCZ', (a, b, c)))
    return g


def compose(a, b):
    """first a then b"""
    pa, sa = a
    pb, sb = b
    p = [pb[pa[i]] for i in range(N)]
    s = [sa[i] * sb[pa[i]] for i in range(N)]
    return p, s


def random_vz(gens, steps=200):
    x = (list(range(N)), [1] * N)
    for _ in range(steps):
        x = compose(x, random.choice(gens))
    return x


if __name__ == '__main__':
    random.seed(1)
    gens = vz_gens()
    order_vz = ss.order([to_perm32(*g) for g in gens])
    print('|V_Z| =', order_vz, ' 2^15·16!/2 =', 2 ** 15 * factorial(16) // 2, flush=True)
    eh = [g for g in gens if conj_is_sp(*g)]
    print('generators of V_Z in E_h:', len(eh), flush=True)
    found = list(eh)
    for _ in range(4000):
        x = random_vz(gens, 60)
        if conj_is_sp(*x):
            found.append(x)
    oe = ss.order([to_perm32(*g) for g in found])
    print('|E_h| >=', oe, ' neighbours <=', order_vz // oe, flush=True)
