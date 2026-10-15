"""W(E8) as the CCX+HH circuit group on three wires: roots, a simple
system with short circuits, and reduced words for the gates.

Vectors are integer 8-tuples at scale 2 (so the roots are the E8
roots doubled: 2(±e_i ± e_j) and (±1)^8).  Basis index x = (x2 x1 x0),
wire 0 the least significant bit.  Letters are the eight generators of
Gen 3 in the Agda development: X0 X1 X2 CX0 CX1 CCX0 HH0 HH1, where CXi
targets wire i with control i+1, CCX0 targets 0 with controls 1, 2, and
HHi acts on wires i, i+1.  A word w = g1 ... gk denotes the matrix
product G1 ... Gk (gk acts first on vectors).
"""
from fractions import Fraction
from itertools import product
import sys

N = 8

def flip(v, t, ctrls=()):
    out = list(v)
    for i in range(N):
        if all(i >> c & 1 for c in ctrls):
            out[i ^ (1 << t)] = v[i]
    return tuple(out)

def hh(v, a, b):
    out = list(v)
    mask = (1 << a) | (1 << b)
    for base in range(N):
        if base & mask:
            continue
        idx = [base | ((r & 1) << a) | ((r >> 1) << b) for r in range(4)]
        for r, i in enumerate(idx):
            num = sum((-1) ** (bin(r & c).count('1')) * v[j] for c, j in enumerate(idx))
            assert num % 2 == 0, (v, a, b)
            out[i] = num // 2
    return tuple(out)

LETTERS = ['X0', 'X1', 'X2', 'CX0', 'CX1', 'CCX0', 'HH0', 'HH1']
ACT = {
    'X0': lambda v: flip(v, 0), 'X1': lambda v: flip(v, 1), 'X2': lambda v: flip(v, 2),
    'CX0': lambda v: flip(v, 0, (1,)), 'CX1': lambda v: flip(v, 1, (2,)),
    'CCX0': lambda v: flip(v, 0, (1, 2)),
    'HH0': lambda v: hh(v, 0, 1), 'HH1': lambda v: hh(v, 1, 2),
}

def act_word(word, v):
    for g in reversed(word):
        v = ACT[g](v)
    return v

def dot(u, v):
    return sum(a * b for a, b in zip(u, v))

def neg(v):
    return tuple(-a for a in v)

def reflect(r, v):
    # s_r(v) = v - 2<v,r>/<r,r> r ; roots have <r,r> = 8 at scale 2
    rr = dot(r, r)
    c = Fraction(2 * dot(v, r), rr)
    out = tuple(a - c * b for a, b in zip(v, r))
    assert all(x.denominator == 1 for x in map(Fraction, out))
    return tuple(int(x) for x in out)

E = [tuple(2 if j == i else 0 for j in range(N)) for i in range(N)]
ROOT_CCX = tuple(a - b for a, b in zip(E[6], E[7]))   # CCX0 swaps |110>,|111>

def root_orbit():
    """Roots reachable from ROOT_CCX by the letters, with shortest words."""
    word = {ROOT_CCX: []}
    frontier = [ROOT_CCX]
    while frontier:
        new = []
        for r in frontier:
            for g in LETTERS:
                s = ACT[g](r)
                if s not in word:
                    word[s] = [g] + word[r]     # s = g(r): w' = g w
                    new.append(s)
        frontier = new
    return word

def canon(r):
    """The root up to sign, with its first nonzero entry positive."""
    for a in r:
        if a != 0:
            return r if a > 0 else neg(r)

if __name__ == '__main__':
    W = root_orbit()
    print('roots:', len(W))
    kinds = {}
    for r in W:
        k = tuple(sorted(abs(a) for a in r))
        kinds[k] = kinds.get(k, 0) + 1
    print('kinds:', kinds)
    minus = {}
    for r in W:
        if all(abs(a) == 1 for a in r):
            m = sum(1 for a in r if a < 0)
            minus[m % 2] = minus.get(m % 2, 0) + 1
    print('spinor roots by parity of minus count:', minus)
    # each gate letter as a reflection? check which are reflections
    for g in LETTERS:
        img = [ACT[g](e) for e in E]
        fixed = sum(1 for i in range(N) if img[i] == E[i])
        print(g, 'fixes', fixed, 'basis vectors')
