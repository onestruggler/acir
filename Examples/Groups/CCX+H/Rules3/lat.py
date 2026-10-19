"""Exact 8-dim vectors over Z[1/sqrt2]; E8 roots; gate actions; lattice orbits.

A number a + b*sqrt2 (a, b Fractions) is a pair.  Basis index = bits,
wire 0 least significant.  Gates: X i, CX i (target i, control i+1),
CXr i (target i+1, control i), CCX (target 0), H i, and conjugates.
"""
from fractions import Fraction as F
import itertools

Z0 = (F(0), F(0))
ONE = (F(1), F(0))

def add(x, y): return (x[0]+y[0], x[1]+y[1])
def sub(x, y): return (x[0]-y[0], x[1]-y[1])
def neg(x): return (-x[0], -x[1])
def over_r2(x): return (x[1], x[0]/2)

def flip(v, t, ctrls=()):
    out = list(v)
    for i in range(8):
        if all(i >> c & 1 for c in ctrls):
            out[i] = v[i ^ (1 << t)]
    return tuple(out)

def had(v, w):
    out = list(v)
    for i in range(8):
        if i >> w & 1: continue
        j = i | (1 << w)
        out[i] = over_r2(add(v[i], v[j]))
        out[j] = over_r2(sub(v[i], v[j]))
    return tuple(out)

def zgate(v, w, ctrls=()):
    return tuple(neg(v[i]) if (i >> w & 1) and all(i >> c & 1 for c in ctrls) else v[i] for i in range(8))

# gate name -> action on vectors
G = {}
for i in range(3):
    G[f"X{i}"] = (lambda v, i=i: flip(v, i))
    G[f"H{i}"] = (lambda v, i=i: had(v, i))
    G[f"Z{i}"] = (lambda v, i=i: zgate(v, i))
for t in range(3):
    for c in range(3):
        if t != c:
            G[f"CX{t}{c}"] = (lambda v, t=t, c=c: flip(v, t, (c,)))
            G[f"CZ{t}{c}"] = (lambda v, t=t, c=c: zgate(v, t, (c,)))
for t in range(3):
    cs = tuple(c for c in range(3) if c != t)
    G[f"CCX{t}"] = (lambda v, t=t, cs=cs: flip(v, t, cs))
G["CCZ"] = lambda v: zgate(v, 0, (1, 2))
for a, b in [(0, 1), (1, 2), (0, 2)]:
    G[f"HH{a}{b}"] = (lambda v, a=a, b=b: had(had(v, a), b))
G["HHH"] = lambda v: had(had(had(v, 0), 1), 2)

def apply(word, v):
    for g in word.split():
        v = G[g](v)
    return v

def vec(ints, den=1):
    return tuple((F(x, den), F(0)) for x in ints)

def e8_roots():
    R = []
    for i, j in itertools.combinations(range(8), 2):
        for si in (1, -1):
            for sj in (1, -1):
                v = [0]*8; v[i] = si; v[j] = sj
                R.append(vec(v))
    for signs in itertools.product((1, -1), repeat=8):
        if signs.count(-1) % 2 == 0:
            R.append(vec(signs, 2))
    return R

def canon(S):
    return frozenset(S)

def orbit(start, gens, limit=10**6):
    """orbit of a set-of-vectors object under gate names gens (left action)."""
    seen = {start: ""}
    frontier = [start]
    while frontier:
        new = []
        for S in frontier:
            for g in gens:
                T = frozenset(G[g](v) for v in S)
                if T not in seen:
                    seen[T] = (g + " " + seen[S]).strip()
                    new.append(T)
                    if len(seen) > limit:
                        return seen
        frontier = new
    return seen

THETA = ["X0", "X1", "X2", "CX01", "CX12", "CX10", "CX21", "CX02", "CX20",
         "CCX0", "HH01", "HH12", "HH02"]
CLIFF = ["X0", "X1", "X2", "CX01", "CX12", "CX10", "CX21", "CX02", "CX20",
         "H0", "H1", "H2"]

if __name__ == "__main__":
    import sys
    E = canon(e8_roots())
    # sanity: Theta fixes E
    for g in THETA:
        assert frozenset(G[g](v) for v in E) == E, g
    print("Theta fixes E8")
    oc = orbit(E, CLIFF)
    print("C3-orbit of E8:", len(oc), "=> |C3 cap Theta| =", 5160960 / len(oc))
    H0E = frozenset(G["H0"](v) for v in E)
    ot = orbit(H0E, THETA)
    print("Theta-orbit of H0 E8:", len(ot), "=> |Theta cap H0 Theta H0| =", 696729600 / len(ot))
