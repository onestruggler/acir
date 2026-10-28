# Generate QCert/HadamardPi/Case34Der.lean: the derivations of Clement's Case 3.4 on the
# indices 0, 1, ... of a sorted window.  Run `python gen_case34der.py ../Case34Der.lean` in `gen/`.
#
# Words are in written order (the rightmost letter acts first).  The joins of Case 3.4 are
# `D ++ A ≈ B` with A = H13 H02 (from s to sigma) and B = H13 H02 H01 (from s to rho); the
# normalisations are transfers along a monomial word m, `A' ++ m ≈ mu ++ A`.
import sys, itertools
from deriv import H, X, Z, parse, fmt
from q2 import matrix
from lib import Lib

def seq(s):
    """application order (first applied first) -> written order"""
    return tuple(reversed(parse(s)))

A = parse("H13 H02")
B = parse("H13 H02 H01")
Bne = parse("H12 H03 H01")

def mono_word(M, m, maxlen=6):
    """a word of X and Z letters with matrix M (breadth first)"""
    letters = [Z(a) for a in range(m)] + [X(a, b) for a, b in itertools.combinations(range(m), 2)]
    if matrix((), m) == M: return ()
    frontier = [()]
    seen = {matrix((), m)}
    for _ in range(maxlen):
        nxt = []
        for w in frontier:
            for l in letters:
                w2 = w + (l,)
                M2 = matrix(w2, m)
                if M2 == M: return w2
                if M2 in seen: continue
                seen.add(M2); nxt.append(w2)
        frontier = nxt
    raise ValueError("no monomial word")

def inv(w): return tuple(reversed(w))

lib = Lib()
# the lemmas of Derived.lean available to the search
for (name, k, L, R) in [
        ("c20", 4, parse("H01 H02 H13 H01 Z0 Z1 H02 H13"), parse("H02 H13 H01 Z0 Z1 H02 H13 H01")),
        ("c21", 6, parse("H01 H02 H13 H04 H15 H01 Z0 Z1 H04 H15 H02 H13"),
         parse("H02 H13 H04 H15 H01 Z0 Z1 H04 H15 H02 H13 H01")),
        ("d4f", 6, parse("H02 H13 H01 H02 H13 H04 H15 H01 H04 H15 H02 H13 H01 H02 H13"),
         parse("H24 H35 H45 H24 H35")),
        ("tt", 6, parse("H02 H13 H01 H02 H13 H02 H13 H01 H02 H13"), ()),
        ("ttp", 6, parse("H04 H15 H01 H04 H15 H04 H15 H01 H04 H15"), ())]:
    lib.lemmas.append((name, k, L, R))

out = []
def transfer(name, m4, Ap, Bp, Aw, Bw, m=4):
    """A' m ≈ mu A and B' m ≈ nu B"""
    mu = mono_word(matrix(Ap + m4 + inv(Aw), m), m)
    nu = mono_word(matrix(Bp + m4 + inv(Bw), m), m)
    lib.add(f"c34_{name}_A", m, Ap + m4, mu + Aw, maxd=8, maxlen=len(Ap + m4) + 6,
            doc=f"`{fmt(Ap + m4)} ≈ {fmt(mu + Aw)}`.")
    lib.add(f"c34_{name}_B", m, Bp + m4, nu + Bw, maxd=8, maxlen=len(Bp + m4) + 6,
            doc=f"`{fmt(Bp + m4)} ≈ {fmt(nu + Bw)}`.")
    out.append((name, m4, mu, nu))

transfer("tr57", parse("Z1"), A, B, A, Bne)
lib.add("c34_conjXX", 4, parse("H13 H02 X01 X23"), parse("X01 X23 H02 H13"), maxd=8, maxlen=10,
        doc="`H13 H02 X01 X23 ≈ X01 X23 H02 H13`.")
mu59 = parse("Z1 Z3 X13 X01 X23")
assert matrix(A + parse("Z1 X01 X23") + inv(A), 4) == matrix(mu59, 4)
lib.add("c34_tr59_A", 4, A + parse("Z1 X01 X23"), mu59 + A,
        chain=[parse("Z1 Z3 X13 H13 H02 X01 X23"), parse("Z1 Z3 X13 X01 X23 H02 H13")], maxd=6,
        doc="`H13 H02 Z1 X01 X23 ≈ Z1 Z3 X13 X01 X23 H13 H02`.")
nu59 = mono_word(matrix(B + parse("Z1 X01 X23") + inv(B), 4), 4)
print("nu59", fmt(nu59))
mu2 = mono_word(matrix(parse("H01 Z0 H01"), 2), 2)
lib.add("c34_hz0", 2, parse("H01 Z0"), mu2 + parse("H01"), maxd=10, maxlen=8,
        doc=f"`H01 Z0 ≈ {fmt(mu2)} H01`.")
mup = mono_word(matrix(parse("H02 Z0 H02"), 4), 4)
w4 = mup + parse("X01 X23 H02 H13 H01")
nu59 = mono_word(matrix(w4 + inv(B), 4), 4)
lib.add("c34_tr59_B", 4, B + parse("Z1 X01 X23"), nu59 + B,
        chain=[parse("H13 H02 X01 Z1 X23 H01"), parse("H13 H02 Z0 X01 X23 H01"),
               mup + parse("H13 H02 X01 X23 H01"), w4], maxd=6, maxlen=14,
        doc=f"`{fmt(B + parse('Z1 X01 X23'))} ≈ {fmt(nu59 + B)}`.")
out.append(("tr59", parse("Z1 X01 X23"), mu59, nu59))
transfer("trZ2", parse("Z2"), A, B, A, B)
transfer("trZ3", parse("Z3"), A, B, A, B)
for name, m4, mu, nu in out:
    print(name, fmt(m4), "mu", fmt(mu), "nu", fmt(nu))

LEAVES = {
    "l341": (4, "H01 Z0 Z1 H13 H02 H01 H02 H13 Z0 Z1 H01"),
    "l21a": (6, "H04 H15 H01 Z0 Z1 H15 H04 H13 H02 H01 H02 H13 H04 H15 Z0 Z1 H01 H15 H04"),
    "l21b": (6, "H04 H15 H01 H15 H04 H13 H02 H01 H02 H13 H24 H35 H45 H35 H24"),
    "l22a": (6, "H05 H14 H04 Z0 Z4 H14 H05 H13 H02 H01 H02 H13 H05 H14 Z0 Z4 H04 H14 H05"),
    "l22b": (6, "H05 H14 H04 H14 H05 H13 H02 H01 H02 H13 H25 H34 H35 X35 Z3 H34 H25"),
}
for name, (m, s) in LEAVES.items():
    D = seq(s)
    assert matrix(D + A, m) == matrix(B, m), name

def leaf(name, chain, **kw):
    m, s = LEAVES[name]
    D = seq(s)
    lib.add("c34_" + name, m, D + A, B, chain=chain, doc=f"The join `{name}`: `D A ≈ B` for `D = {fmt(D)}`.", **kw)

leaf("l341", [parse("H01 Z1 Z0 H13 H02 H01 H02 H13 H01 Z0 Z1 H02 H13"),
              parse("H01 Z1 Z0 H13 H02 H02 H13 H01 Z0 Z1 H02 H13 H01"),
              parse("H01 Z1 Z0 H01 Z0 Z1 H02 H13 H01"), parse("H02 H13 H01")], maxd=6)
L9 = "H04 H15 H01 Z1 Z0 H15 H04 H13 H02 "
leaf("l21a", [parse(L9 + "H01 H02 H13 H04 H15 H01 Z0 Z1 H04 H15 H02 H13"),
              parse(L9 + "H02 H13 H04 H15 H01 Z0 Z1 H04 H15 H02 H13 H01"),
              parse("H04 H15 H01 Z1 Z0 H01 Z0 Z1 H04 H15 H02 H13 H01"),
              parse("H04 H15 H01 H01 H04 H15 H02 H13 H01"), parse("H02 H13 H01")], maxd=6)
T = "H02 H13 H01 H02 H13 "; Tp = "H04 H15 H01 H04 H15 "
leaf("l21b", [parse("H24 H35 H45 H24 H35 H13 H02 H01 H02 H13 H04 H15 H01 H15 H04 H13 H02"),
              parse(T + Tp + T + "H13 H02 H01 H02 H13 H04 H15 H01 H15 H04 H13 H02"),
              parse(T + Tp + T + T + "H04 H15 H01 H15 H04 H13 H02"),
              parse(T + Tp + "H04 H15 H01 H15 H04 H13 H02"),
              parse(T + Tp + Tp + "H13 H02"), parse(T + "H13 H02"), parse("H02 H13 H01")], maxd=6)

# Lemma 3.17's (31) and (33): conjugates of (30) and (32) by the signed transposition
# pi = (-1)[4] X[4,5], up to three-index identities from H12 Z2 H12 = X12.
lib.add("c34_core3", 3, parse("Z2 H12 H01 Z0 Z1 H12 Z2"), parse("H12 H02 Z0 Z2 H12"),
        chain=[parse("H12 X12 H01 Z0 Z1 X12 H12")], maxd=8, doc="`Z2 H12 H01 Z0 Z1 H12 Z2 ≈ H12 H02 Z0 Z2 H12`.")
lib.add("c34_core3b", 3, parse("Z2 H12 H01 H12 Z2"), parse("H12 H02 H12"),
        chain=[parse("H12 X12 H01 X12 H12")], maxd=8, doc="`Z2 H12 H01 H12 Z2 ≈ H12 H02 H12`.")
lib.add("c34_conjH", 4, parse("X23 H02 H13 X23"), parse("H03 H12"), maxd=8, maxlen=8,
        doc="`X23 H02 H13 X23 ≈ H03 H12`.")
lib.add("c34_rot31", 4, parse("H03 H12 H02 Z0 Z2 H03 H12"),
        parse("Z2 X23 H02 H13 H01 Z0 Z1 H02 H13 X23 Z2"),
        chain=[parse("H03 H12 H02 Z0 Z2 H12 H03"), parse("H03 Z2 H12 H01 Z0 Z1 H12 Z2 H03"),
               parse("Z2 H03 H12 H01 Z0 Z1 H03 H12 Z2"),
               parse("Z2 X23 H02 H13 X23 H01 Z0 Z1 X23 H02 H13 X23 Z2")], maxd=6,
        doc="`H03 H12 H02 Z0 Z2 H03 H12 ≈ π H02 H13 H01 Z0 Z1 H02 H13 π` with `π = Z2 X23`.")
lib.add("c34_rot32", 4, parse("H03 H12 H02 H03 H12"), parse("Z2 X23 H02 H13 H01 H02 H13 X23 Z2"),
        chain=[parse("H03 H12 H02 H12 H03"), parse("H03 Z2 H12 H01 H12 Z2 H03"),
               parse("Z2 H03 H12 H01 H03 H12 Z2"),
               parse("Z2 X23 H02 H13 X23 H01 X23 H02 H13 X23 Z2")], maxd=6,
        doc="`H03 H12 H02 H03 H12 ≈ π H02 H13 H01 H02 H13 π` with `π = Z2 X23`.")
lib.add("c34_vcv3", 3, parse("Z1 H01 X12 H12 X12 H01 Z1"), parse("H01 Z0 X02 H02 H01"), maxd=10, maxlen=12,
        doc="`Z1 H01 X12 H12 X12 H01 Z1 ≈ H01 Z0 X02 H02 H01`.")
lib.add("c34_vcv", 6, parse("H25 H34 Z3 X35 H35 H34 H25"), parse("Z4 X45 H24 H35 H45 H35 H24 X45 Z4"),
        chain=[parse("H25 Z4 H34 X45 H45 X45 H34 Z4 H25")], maxd=8,
        doc="`H25 H34 Z3 X35 H35 H34 H25 ≈ π H24 H35 H45 H35 H24 π` with `π = Z4 X45`.")
P1 = "Z4 X45 H04 H15 H01 Z0 Z1 H04 H15 X45 Z4 "
D21a = " ".join(f"{l[0]}{l[1]}{l[2]}" if l[0] != 'Z' else f"Z{l[1]}" for l in seq(LEAVES["l21a"][1]))
leaf("l22a", [parse("H05 H14 H04 Z0 Z4 H05 H14 H13 H02 H01 H02 H13 H05 H14 H04 Z0 Z4 H05 H14 H13 H02"),
              parse(P1 + "H13 H02 H01 H02 H13 " + P1 + "H13 H02"),
              parse("Z4 X45 H04 H15 H01 Z0 Z1 H04 H15 H13 H02 H01 H02 H13 X45 Z4 Z4 X45 "
                    "H04 H15 H01 Z0 Z1 H04 H15 X45 Z4 H13 H02"),
              parse("Z4 X45 H04 H15 H01 Z0 Z1 H04 H15 H13 H02 H01 H02 H13 "
                    "H04 H15 H01 Z0 Z1 H04 H15 X45 Z4 H13 H02"),
              parse("Z4 X45 H04 H15 H01 Z0 Z1 H04 H15 H13 H02 H01 H02 H13 "
                    "H04 H15 Z0 Z1 H01 H04 H15 X45 Z4 H13 H02"),
              parse("Z4 X45 " + D21a + " H13 H02 X45 Z4"),
              parse("Z4 X45 H13 H02 H01 X45 Z4"),
              parse("Z4 X45 X45 Z4 H13 H02 H01")], maxd=6)
D21b = " ".join(f"{l[0]}{l[1]}{l[2]}" if l[0] != 'Z' else f"Z{l[1]}" for l in seq(LEAVES["l21b"][1]))
leaf("l22b", [parse("Z4 X45 H24 H35 H45 H35 H24 X45 Z4 H13 H02 H01 H02 H13 H05 H14 H04 H05 H14 H13 H02"),
              parse("Z4 X45 H24 H35 H45 H35 H24 X45 Z4 H13 H02 H01 H02 H13 "
                    "Z4 X45 H04 H15 H01 H04 H15 X45 Z4 H13 H02"),
              parse("Z4 X45 H24 H35 H45 H35 H24 H13 H02 H01 H02 H13 X45 Z4 "
                    "Z4 X45 H04 H15 H01 H04 H15 X45 Z4 H13 H02"),
              parse("Z4 X45 H24 H35 H45 H35 H24 H13 H02 H01 H02 H13 "
                    "H04 H15 H01 H04 H15 X45 Z4 H13 H02"),
              parse("Z4 X45 " + D21b + " H13 H02 X45 Z4"),
              parse("Z4 X45 H13 H02 H01 X45 Z4"),
              parse("Z4 X45 X45 Z4 H13 H02 H01")], maxd=6)
print("all derived")

header = """/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The derivations of Clement's Case 3.4

Generated by `gen/gen_case34der.py` (run `python gen_case34der.py ../Case34Der.lean` in
`gen/`); do not edit by hand.

On a window `0, 1, 2, 3, ...` of the pivot column with `A = H_[1,3] H_[0,2]` (from `s` to
`sigma`) and `B = H_[1,3] H_[0,2] H_[0,1]` (from `s` to `rho`):

* the normalisations of Clement's Lemmas 5.7 and 5.9 and Assumption 3 are transfers along a
  monomial word `m`, with `A' m ≈ mu A` and `B' m ≈ nu B` (`c34_tr57_A`, ..., `c34_trZ3_B`);
* the joins of Subcases 3.4.1 (`c34_l341`, by Clement's relation (20)), 3.4.2.1 (`c34_l21a`,
  by (21); `c34_l21b`, by (d4) as `T T' T ≈ V C V`) and 3.4.2.2 (`c34_l22a`, `c34_l22b`) are
  `D A ≈ B`.  The paths of 3.4.2.2 are Clement's diagrams (31) and (33) of Lemma 3.17, whose
  relations are those of (30) and (32) conjugated by the signed transposition
  `pi = (-1)_[4] X_[4,5]`, up to three-index identities that follow from
  `H_[1,2] (-1)_[2] H_[1,2] = X_[1,2]` (`c34_core3`, `c34_rot31`, `c34_rot32`, `c34_vcv`);
  Clement's `H[5,3]` is written `(-1)_[3] X_[3,5] H_[3,5]`.
-/
import QCert.HadamardPi.Derived

namespace QCert.HadamardPi

open FreeMonoid

"""
open(sys.argv[1], "w", encoding="utf-8", newline="\n").write(
    header + lib.text() + "\nend QCert.HadamardPi\n")
print("written", sys.argv[1])
