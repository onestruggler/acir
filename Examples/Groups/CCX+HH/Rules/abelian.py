#!/usr/bin/env python3
"""Abelianization of the group presented by placed rules, at any width.

Every generator is an involution, so a character of the presented group
is an assignment χ of 0 or 1 to the gates (on every wire placement) with
χ(r) = 0 mod 2 for every relator r, definitions expanded.  From four
wires on the true group is perfect (GeneralN/Perfect.agda), so a rule
set with a nonzero character there is incomplete.  This is the cheapest
refutation available where coset enumeration is not (the group being
infinite).

Run: python3 -B abelian.py
"""

import core as C
import staged as S

# The twelve rules complete on one to three wires (README), and the
# definition of the swap letter they use.
TWELVE = [
    "SW0 = CX0 CXr0 CX0",
    "X1 CX0 X1 = CX0 X0",
    "CXr0 X0 CXr0 = X0 X1",
    "CX0 CXr0 CX0 CXr0 CX0 CXr0",
    "X0 HH0 X1 HH0 = HH0 X1 HH0 X0",
    "SW0 SW1 SW0 = SW1 SW0 SW1",
    "SW0 SW1 CX0 SW1 SW0 = CX1",
    "SW1 CCX0 SW1 = CCX0",
    "X1 CCX0 X1 = CCX0 SW1 CX0 SW1",
    "CCX0 CXr0 CCX0 CXr0 = SW0 CCX0 SW0 CCX0",
    "SW0 HH1 SW0 = HH0 HH1",
    "SW1 HH0 SW1 = HH0 HH1",
    "CCX0 CXr0 HH0 CXr0 = CXr0 HH0 CXr0 CCX0",
]

# A Toffoli is the commutator of a Toffoli and a CNOT (four wires).
TOFFOLI_COMMUTATOR = "CCX1 CX0 CCX1 CX0 = SW0 CCX1 SW0"


def alphabet(n):
    gs = C.GateSet(n)
    derived = {}
    for i in range(n - 1):
        derived[f"CXr{i}"] = f"HH{i} CX{i} HH{i}"
        derived[f"SW{i}"] = f"CX{i} HH{i} CX{i} HH{i} CX{i}"
    return gs, S.Alphabet(gs, derived)


def characters(n, texts):
    """A basis of the characters, each as the set of gates it counts."""
    gs, a = alphabet(n)
    g = len(gs.names)
    rows = []
    for t in texts:
        for r in S.rule(a, t):
            v = 0
            for x in a.primitive(r):
                v ^= 1 << x
            rows.append(v)
    # Gaussian elimination to reduced row echelon form over F_2.
    pivots = {}
    for v in rows:
        for col, b in pivots.items():
            if v >> col & 1:
                v ^= b
        if v:
            col = v.bit_length() - 1
            for c2 in list(pivots):
                if pivots[c2] >> col & 1:
                    pivots[c2] ^= v
            pivots[col] = v
    free = [c for c in range(g) if c not in pivots]
    basis = []
    for f in free:
        chi = {f}
        for col, b in pivots.items():
            if b >> f & 1:
                chi.add(col)
        basis.append(sorted(gs.names[c] for c in chi))
    return basis


def sound(n, text):
    """Exact soundness at any width: both sides act alike on every basis
    vector (scaled by 2^k so that every H ⊗ H step stays integral)."""
    gs, a = alphabet(n)
    out = []
    for r in S.rule(a, text):
        w = a.primitive(r)
        k = sum(1 for g in w if gs.names[g].startswith("HH"))
        dim = 1 << n
        for i in range(dim):
            v = tuple((2 ** k) if j == i else 0 for j in range(dim))
            u = v
            for g in reversed(w):
                u = gs.actions[g](u)
            out.append(u == v)
    return all(out) and bool(out)


# Two spellings of the cycle carrying wires 0, 1, 2 to 1, 2, 3.
CCX_UP = "SW0 SW1 SW2 CCX0 SW2 SW1 SW0 = CCX1"   # sound; the reverse spelling is not


if __name__ == "__main__":
    for n in (3, 4, 5):
        print(f"{n} wires, the twelve rules: characters {characters(n, TWELVE)}")
    four = [TOFFOLI_COMMUTATOR, CCX_UP]
    assert all(sound(4, t) for t in four) and all(sound(4, t) for t in TWELVE)
    for n in (4, 5, 6):
        print(f"{n} wires, with the two four-wire rules: "
              f"characters {characters(n, TWELVE + four)}")
