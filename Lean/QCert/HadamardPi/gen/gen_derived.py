# Generate QCert/HadamardPi/Derived.lean: derived relations of Figure 6 on four indices, and
# Clément's relation (20).  Run `python gen_derived.py ../Derived.lean` in `gen/`.
import sys
from deriv import H, X, Z, parse
from lib import Lib

A = (H(0, 1),); B = (H(2, 3),); Q = (H(0, 2), H(1, 3)); Qr = (H(1, 3), H(0, 2))
BQ = B + Q
F1A = (H(0, 1), H(2, 3), H(0, 2), H(1, 3)) * 2

lib = Lib()
# (f1) at (0,1,2,3) is `f1₀` of Switch.lean
lib.lemmas.append(("f1₀", 4, F1A, ()))

lib.add("d3exp", 4, A, BQ * 4 + B, maxd=4,
        doc="`H_[0,1] ≈ (H_[2,3] H_[0,2] H_[1,3])⁴ H_[2,3]`, by (d3).")
lib.add("bq8", 4, BQ * 8, (), chain=[A + B + BQ * 4, A + B + A + B, A + A + B + B], maxd=4,
        doc="`(H_[2,3] H_[0,2] H_[1,3])⁸ ≈ ε`, by (d3) twice.")
# h0: A Q B Qr A ≈ Q A Q, both sides to (BQ)² B
left = [BQ * 4 + B + Q + B + Q + A,
        BQ * 4 + B + Q + B + Q + BQ * 4 + B,
        BQ * 2 + B]
right_rev = []
v1 = Q + BQ * 4 + B + Q                       # Q A Q with A expanded
us = [BQ * (8 - k) + (Q + B) * (5 - k) + Q for k in range(6)]
# from (BQ)^2 B back up to Q A Q
right = [BQ * 3 + Q] + list(reversed(us)) + [v1]
lib.add("h0", 4, A + Q + B + Qr + A, Q + A + Q, chain=left + right, maxd=5,
        doc="Proposition h0 of the paper, `H_[0,1] H_[0,2] H_[1,3] H_[2,3] H_[1,3] H_[0,2] H_[0,1] ≈ "
            "H_[0,2] H_[1,3] H_[0,1] H_[1,3] H_[0,2]` (by (d3)).")
lib.add("qa", 4, Q + A, B + A + Q + B, maxd=10, maxlen=12,
        doc="`H_[0,2] H_[1,3] H_[0,1] ≈ H_[2,3] H_[0,1] H_[0,2] H_[1,3] H_[2,3]`, by (f1).")
Zs = (Z(0), Z(1))
M = parse("Z0 Z1 Z2 Z3 X02 X13")
lib.add("qzq", 4, Q + Zs + Q, M,
        chain=[parse("H02 Z0 H02 H13 Z1 H13"), parse("Z0 Z2 X02 H02 H02 H13 Z1 H13"),
               parse("Z0 Z2 X02 Z1 Z3 X13 H13 H13"), parse("Z0 Z2 X02 Z1 Z3 X13")], maxd=6,
        doc="`H_[0,2] H_[1,3] (-1)_[0] (-1)_[1] H_[0,2] H_[1,3]` is a signed permutation.")
lib.add("ma", 4, M + A, B + M, maxd=10, maxlen=12,
        doc="The signed permutation of `qzq` carries `H_[0,1]` to `H_[2,3]`.")
lib.add("qbqa", 4, Q + B + Q + A, Q + A + Q + B, chain=[Q + B + B + A + Q + B], maxd=6,
        use=None, doc="`Q B Q A ≈ Q A Q B` with `Q = H_[0,2] H_[1,3]`, `A = H_[0,1]`, `B = H_[2,3]`.")
L20 = A + Q + A + Zs + Q
R20 = Q + A + Zs + Q + A
chain20 = [A + Q + A + Q + Q + Zs + Q,
           A + A + Q + B + Qr + A + Q + Zs + Q,
           Q + B + Qr + A + Q + Zs + Q,
           Q + B + Q + A + M,
           Q + A + Q + B + M,
           Q + A + Q + M + A,
           Q + A + Q + Q + Zs + Q + A]
lib.add("c20", 4, L20, R20, chain=chain20, maxd=6,
        doc="Clément's relation (20), `H[0,1] H[0,2] H[1,3] H[0,1] (-1)[0] (-1)[1] H[0,2] H[1,3] ≈ "
            "H[0,2] H[1,3] H[0,1] (-1)[0] (-1)[1] H[0,2] H[1,3] H[0,1]`.")

# ---- six indices: Clément's (21) from (d4) ----
lib.add("xz0", 2, parse("X01 Z0"), parse("Z1 X01"), maxd=5, doc="`X_[0,1] (-1)_[0] ≈ (-1)_[1] X_[0,1]`.")
lib.add("zhz", 2, parse("Z0 H01 Z0"), parse("Z1 X01 H01"), maxd=6,
        doc="`(-1)_[0] H_[0,1] (-1)_[0] ≈ (-1)_[1] X_[0,1] H_[0,1]`.")
lib.add("rev3", 3, parse("X02 H01 X02"), parse("X12 H12 X12"), maxd=8, maxlen=10,
        doc="`X_[0,2] H_[0,1] X_[0,2] ≈ X_[1,2] H_[1,2] X_[1,2]` (both are `H_[2,1]`).")
lib.add("zv4", 4, parse("Z0 Z1 Z2 Z3 H02 H13"), parse("H02 H13 Z0 Z1 Z2 Z3"),
        chain=[parse("Z1 Z3 Z0 Z2 H02 H13"), parse("Z1 Z3 H02 Z0 Z2 H13"), parse("H02 Z1 Z3 H13 Z0 Z2"),
               parse("H02 H13 Z1 Z3 Z0 Z2")], maxd=5, doc="Signs on all four indices pass `H_[0,2] H_[1,3]`.")
lib.add("zc4", 4, parse("Z0 Z1 Z2 Z3 H23"), parse("H23 Z0 Z1 Z2 Z3"), chain=[parse("Z0 Z1 H23 Z2 Z3")], maxd=5,
        doc="Signs on all four indices pass `H_[2,3]`.")
lib.add("zz4", 4, parse("Z0 Z1 Z2 Z3 Z0 Z1 Z2 Z3"), (), chain=[parse("Z0 Z0 Z1 Z1 Z2 Z2 Z3 Z3")], maxd=5,
        doc="Signs on all four indices square to `ε`.")
lib.add("mswap4", 4, M, parse("X02 X13 Z0 Z1 Z2 Z3"),
        chain=[parse("Z0 Z1 Z2 X02 Z3 X13"), parse("Z0 Z1 Z2 X02 X13 Z1"), parse("Z0 Z2 X02 Z1 X13 Z1"),
               parse("Z0 Z2 X02 X13 Z3 Z1"), parse("Z0 X02 Z0 X13 Z3 Z1"), parse("X02 Z2 Z0 X13 Z3 Z1"),
               parse("X02 X13 Z2 Z0 Z3 Z1")], maxd=5, doc="The signed permutation `M` in two orders.")
lib.add("mm4", 4, M + M, (), chain=[M + parse("X02 X13 Z0 Z1 Z2 Z3"),
        parse("Z0 Z1 Z2 Z3 X02 X02 X13 X13 Z0 Z1 Z2 Z3"), parse("Z0 Z1 Z2 Z3 Z0 Z1 Z2 Z3")], maxd=6,
        doc="`M M ≈ ε` for the signed permutation `M` of `qzq`.")
lib.add("mbm", 4, A, M + B + M, chain=[M + M + A], maxd=4, doc="`A ≈ M B M`.")
lib.add("qm", 4, Q + M, Zs + Q, chain=[Q + Q + Zs + Q], maxd=5, doc="`Q M ≈ Z Q`.")
lib.add("mq", 4, M + Q, Q + Zs, chain=[Q + Zs + Q + Q], maxd=5, doc="`M Q ≈ Q Z`.")
lib.add("qaqz", 4, Q + A + Q, Zs + Q + B + Q + Zs,
        chain=[Q + M + B + M + Q, Zs + Q + B + M + Q], maxd=6,
        doc="`Q A Q ≈ Z Q B Q Z` with `Z = (-1)_[0] (-1)_[1]`.")

Q6 = parse("H02 H13"); R6 = parse("H04 H15"); A6 = parse("H01"); V6 = parse("H24 H35"); C6 = parse("H45")
B6 = parse("H23"); X6 = parse("X24 X35"); Z6 = parse("Z0 Z1"); Z23 = parse("Z2 Z3"); Z45 = parse("Z4 Z5")
Z2345 = parse("Z2 Z3 Z4 Z5"); M6 = parse("Z0 Z1 Z4 Z5 X04 X15")
T6 = Q6 + A6 + Q6; T6p = R6 + A6 + R6
lib.add("conjX", 6, X6 + T6 + X6, T6p, chain=[R6 + X6 + A6 + Q6 + X6, R6 + A6 + X6 + Q6 + X6, R6 + A6 + R6 + X6 + X6],
        maxd=6, doc="`X T X ≈ T'` with `T = Q A Q`, `T' = R A R`, `X = X_[2,4] X_[3,5]`.")
lib.add("conjX2", 6, X6 + T6p + X6, T6, chain=[X6 + X6 + T6 + X6 + X6], maxd=6, doc="`X T' X ≈ T`.")
lib.add("d4f", 6, T6 + T6p + T6, V6 + C6 + V6,
        chain=[T6 + X6 + X6 + T6p + X6 + X6 + T6 + X6 + X6, T6 + X6 + T6 + X6 + T6 + X6 + X6, V6 + C6 + V6 + X6 + X6],
        maxd=6, doc="(d4) at `0, …, 5` as `T T' T ≈ V C V`, `V = H_[2,4] H_[3,5]`, `C = H_[4,5]`.")
lib.add("xhx", 2, parse("X01 H01 X01"), parse("Z0 H01 Z1"), maxd=8, maxlen=8,
        doc="`X_[0,1] H_[0,1] X_[0,1] ≈ (-1)_[0] H_[0,1] (-1)_[1]`.")
lib.add("xvx", 6, X6 + V6 + X6, Z23 + V6 + Z45,
        chain=[parse("X24 H24 X24 X35 H35 X35"), parse("Z2 H24 Z4 Z3 H35 Z5")], maxd=6,
        doc="`X V X ≈ (-1)_[2] (-1)_[3] V (-1)_[4] (-1)_[5]`.")
lib.add("xcx", 6, X6 + C6 + X6, B6, maxd=8, maxlen=10, doc="`X C X ≈ H_[2,3]`.")
lib.add("xvcvx", 6, X6 + V6 + C6 + V6 + X6, V6 + C6 + V6,
        chain=[X6 + V6 + X6 + X6 + C6 + X6 + X6 + V6 + X6, Z23 + V6 + Z45 + B6 + Z23 + V6 + Z45,
               Z23 + V6 + B6 + Z2345 + V6 + Z45, Z23 + V6 + B6 + V6 + Z2345 + Z45, Z23 + V6 + B6 + V6 + Z23,
               Z23 + Z23 + V6 + C6 + V6 + Z23 + Z23], maxd=6, doc="`X` commutes with `V C V`.")
lib.add("mswap", 6, M6, parse("X04 X15 Z0 Z1 Z4 Z5"),
        chain=[parse("Z0 Z1 Z4 X04 Z5 X15"), parse("Z0 Z1 Z4 X04 X15 Z1"), parse("Z0 Z4 X04 Z1 X15 Z1"),
               parse("Z0 Z4 X04 X15 Z5 Z1"), parse("Z0 X04 Z0 X15 Z5 Z1"), parse("X04 Z4 Z0 X15 Z5 Z1"),
               parse("X04 X15 Z4 Z0 Z5 Z1")], maxd=5, doc="The signed permutation `M'` in two orders.")
lib.add("mm", 6, M6 + M6, (), chain=[M6 + parse("X04 X15 Z0 Z1 Z4 Z5"),
        parse("Z0 Z1 Z4 Z5 X04 X04 X15 X15 Z0 Z1 Z4 Z5"), parse("Z0 Z1 Z4 Z5 Z0 Z1 Z4 Z5"),
        parse("Z0 Z0 Z1 Z1 Z4 Z4 Z5 Z5")], maxd=4, doc="`M' M' ≈ ε`.")
lib.add("rzr", 6, R6 + Z6 + R6, M6, chain=[parse("H04 Z0 H04 H15 Z1 H15"), parse("Z0 Z4 X04 H04 H04 H15 Z1 H15"),
        parse("Z0 Z4 X04 Z1 Z5 X15 H15 H15"), parse("Z0 Z4 X04 Z1 Z5 X15")], maxd=6,
        doc="`R (-1)_[0] (-1)_[1] R ≈ M'`.")
lib.add("mqm", 6, M6 + Q6 + M6, Z2345 + V6,
        chain=[parse("Z0 Z1 Z4 Z5 X04 X15 H02 H13 X04 X15 Z0 Z1 Z4 Z5"),
               parse("Z0 Z1 Z4 Z5 X04 H02 X04 X15 H13 X15 Z0 Z1 Z4 Z5"),
               parse("Z0 Z1 Z4 Z5 X24 H24 X24 X35 H35 X35 Z0 Z1 Z4 Z5"),
               parse("Z4 Z5 X24 H24 X24 X35 H35 X35 Z0 Z1 Z0 Z1 Z4 Z5"),
               parse("Z4 Z5 X24 H24 X24 X35 H35 X35 Z4 Z5"),
               parse("Z4 X24 H24 X24 Z4 Z5 X35 H35 X35 Z5"),
               parse("X24 Z2 H24 Z2 X24 Z5 X35 H35 X35 Z5"),
               parse("X24 Z2 H24 Z2 X24 X35 Z3 H35 Z3 X35"),
               parse("X24 Z4 X24 H24 X24 X35 Z5 X35 H35 X35"),
               parse("Z2 H24 X24 Z3 H35 X35"), parse("Z2 Z4 H24 Z3 Z5 H35")], maxd=6,
        doc="`M' Q M' ≈ (-1)_[2] ⋯ (-1)_[5] V`.")
lib.add("ma6", 6, M6 + A6, C6 + M6, maxd=8, maxlen=12, doc="`M' H_[0,1] ≈ H_[4,5] M'`.")
lib.add("mtm", 6, M6 + T6 + M6, V6 + C6 + V6,
        chain=[M6 + Q6 + M6 + M6 + A6 + M6 + M6 + Q6 + M6, Z2345 + V6 + M6 + A6 + M6 + Z2345 + V6,
               Z2345 + V6 + C6 + M6 + M6 + Z2345 + V6, Z2345 + V6 + C6 + Z2345 + V6,
               V6 + Z2345 + C6 + Z2345 + V6, V6 + C6 + Z2345 + Z2345 + V6], maxd=6, doc="`M' T M' ≈ V C V`.")
lib.add("braid", 6, T6p + T6 + T6p, M6 + T6 + M6,
        chain=[X6 + T6 + T6p + T6 + X6, X6 + V6 + C6 + V6 + X6, V6 + C6 + V6], maxd=6,
        doc="`T' T T' ≈ M' T M'` (both are `V C V`).")
lib.add("tt", 6, T6 + T6, (), chain=[Q6 + A6 + A6 + Q6], maxd=6, doc="`T T ≈ ε`.")
lib.add("ttp", 6, T6p + T6p, (), chain=[R6 + A6 + A6 + R6], maxd=6, doc="`T' T' ≈ ε`.")
Mw = M6
L21 = A6 + Q6 + R6 + A6 + Z6 + R6 + Q6
R21 = Q6 + R6 + A6 + Z6 + R6 + Q6 + A6
chain21 = [A6 + Q6 + R6 + A6 + R6 + Mw + Q6,
           Q6 + Q6 + A6 + Q6 + R6 + A6 + R6 + Mw + Q6,
           Q6 + T6 + T6p + Mw + Q6,
           Q6 + T6p + T6p + T6 + T6p + Mw + Q6,
           Q6 + T6p + Mw + T6 + Mw + Mw + Q6,
           Q6 + T6p + Mw + T6 + Q6,
           Q6 + T6p + Mw + Q6 + A6,
           Q6 + R6 + A6 + R6 + Mw + Q6 + A6]
lib.add("c21", 6, L21, R21, chain=chain21, maxd=6,
        doc="Clément's relation (21), `H[0,1] H[0,2] H[1,3] H[0,4] H[1,5] H[0,1] (-1)[0] (-1)[1] H[0,4] H[1,5] "
            "H[0,2] H[1,3] ≈ H[0,2] H[1,3] H[0,4] H[1,5] H[0,1] (-1)[0] (-1)[1] H[0,4] H[1,5] H[0,2] H[1,3] H[0,1]`.")

header = """/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Derived relations, and Clément's relations (20) and (21)

Generated by `gen/gen_derived.py` (run `python gen_derived.py ../Derived.lean` in
`gen/`); do not edit by hand.

With `A = H_[0,1]`, `B = H_[2,3]`, `Q = H_[0,2] H_[1,3]`: (d3) is
`(B Q)⁴ ≈ A B`, so `A ≈ (B Q)⁴ B` and `(B Q)⁸ ≈ ε` (`d3exp`, `bq8`); the
paper's Proposition h0, `A Q B Q A ≈ Q A Q`, follows by writing both sides as
`(B Q)² B`.  With (f1) (`qa`) and the signed permutation
`Q (-1)_[0] (-1)_[1] Q` (`qzq`, `ma`), this gives Clément's relation (20)
(`c20`): `A Q A Z Q ≈ (A Q B Q A) Q Z Q`-wise, `≈ Q B Q A M ≈ Q A Q B M
≈ Q A Q M A ≈ Q A Z Q A`.

On six indices, with `T = Q A Q`, `T' = R A R`, `R = H_[0,4] H_[1,5]`,
`V = H_[2,4] H_[3,5]`, `C = H_[4,5]`, `X = X_[2,4] X_[3,5]`: (d4) at
`0, …, 5` is `(T X)³ ≈ V C V X`, that is `T T' T ≈ V C V` (`d4f`, as
`X T X ≈ T'`); conjugating by `X`, which commutes with `V C V` (`xvcvx`, by
`qaqz` on `2, 3, 4, 5`), gives the braid `T' T T' ≈ T T' T`, and
`M' T M' ≈ V C V` for the signed permutation `M' = R (-1)_[0] (-1)_[1] R`
(`mtm`).  Clément's (21) says that `A` commutes with `Q T' M' Q`, i.e. that
`T' T T' ≈ M' T M'` (`braid`), whence `c21`.
-/
import QCert.HadamardPi.Switch

namespace QCert.HadamardPi

open FreeMonoid

"""
open(sys.argv[1], "w", encoding="utf-8", newline="\n").write(
    header + lib.text() + "\nend QCert.HadamardPi\n")
print("written", sys.argv[1])
