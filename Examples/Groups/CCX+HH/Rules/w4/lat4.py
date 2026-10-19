"""Four wires: which gates preserve candidate 16-dimensional lattices."""
import itertools
from fractions import Fraction as F
N = 4
D = 16

def bit(x, k): return x >> k & 1

def flip(v, t, cs=()):
    return tuple(v[j ^ (1 << t)] if all(bit(j, c) for c in cs) else v[j] for j in range(D))

def hh(v, a, b):
    out = []
    for i in range(D):
        s = F(0)
        for j in range(D):
            if all(bit(i, k) == bit(j, k) for k in range(N) if k not in (a, b)):
                sg = bit(i, a) * bit(j, a) + bit(i, b) * bit(j, b)
                s += (-v[j] if sg % 2 else v[j]) / 2
        out.append(s)
    return tuple(out)

def swap(v, a, b):
    def f(j):
        return j ^ (1 << a) ^ (1 << b) if bit(j, a) != bit(j, b) else j
    return tuple(v[f(j)] for j in range(D))

G = {}
for i in range(4):
    G[f'X{i}'] = lambda v, i=i: flip(v, i)
for i in range(3):
    G[f'CX{i}'] = lambda v, i=i: flip(v, i, (i + 1,))
    G[f'HH{i}'] = lambda v, i=i: hh(v, i, i + 1)
    G[f'SW{i}'] = lambda v, i=i: swap(v, i, i + 1)
for i in range(2):
    G[f'CCX{i}'] = lambda v, i=i: flip(v, i, (i + 1, i + 2))

def e8_roots():
    R = []
    for i, j in itertools.combinations(range(8), 2):
        for si in (1, -1):
            for sj in (1, -1):
                v = [F(0)] * 8; v[i] = F(si); v[j] = F(sj); R.append(tuple(v))
    for s in itertools.product((1, -1), repeat=8):
        if s.count(-1) % 2 == 0:
            R.append(tuple(F(x, 2) for x in s))
    return R

def member_E8(v):
    if all(x.denominator == 1 for x in v):
        return sum(v) % 2 == 0
    if all(x.denominator == 2 for x in v):
        return sum(v) % 2 == 0
    return False

# candidate: E8 + E8 split by wire 3 (levels 0..7 and 8..15)
def in_E8E8(v):
    return member_E8(v[:8]) and member_E8(v[8:])

def basis_E8E8():
    R = e8_roots()
    out = []
    for r in R:
        out.append(r + (F(0),) * 8)
        out.append((F(0),) * 8 + r)
    return out

# D16+ : D16 + (1/2)^16
def in_D16p(v):
    if all(x.denominator == 1 for x in v):
        return sum(v) % 2 == 0
    if all(x.denominator == 2 for x in v):
        return sum(v) % 2 == 0   # (1/2)^16 has sum 8 even
    return False

def basis_D16p():
    out = []
    for i, j in itertools.combinations(range(16), 2):
        v = [F(0)] * 16; v[i] = F(1); v[j] = F(1); out.append(tuple(v))
        v = [F(0)] * 16; v[i] = F(1); v[j] = F(-1); out.append(tuple(v))
    out.append(tuple(F(1, 2) for _ in range(16)))
    return out

for name, test, basis in [('E8+E8', in_E8E8, basis_E8E8()), ('D16+', in_D16p, basis_D16p())]:
    keep = [g for g in G if all(test(G[g](v)) for v in basis)]
    print(name, 'preserved by', keep)
