# Generate QCert/Clement2019/DerivedC.lean: Figure 6's (d3) on four indices and (d4) on six,
# derived from Clement's relations ((20) and (21) at the placements whose letters are increasing,
# and (1)-(19)).  Run `python gen_derivedc.py ../DerivedC.lean` in `gen/`.
import sys
from clement import CLib, parse

P = parse
lib = CLib()


def add(name, m, L, R, doc, full=False, **kw):
    lib.add("k" + name, m, L, R, full=full, inc=True, doc=doc, **kw)


# ---- four indices ----
A = P("H01"); B = P("H23"); Q = P("H02 H13"); Zs = P("Z0 Z1")
M = P("Z0 Z1 Z2 Z3 X02 X13")
add("zz4", 4, P("Z0 Z1 Z2 Z3 Z0 Z1 Z2 Z3"), (), "Signs on all four indices square to `ε`.",
    chain=[P("Z0 Z0 Z1 Z1 Z2 Z2 Z3 Z3")], maxd=5)
add("qq4", 4, Q + Q, (), "`Q Q ≈ ε` with `Q = H[0,2] H[1,3]`.", maxd=4)
add("qzq", 4, Q + Zs + Q, M, "`Q (-1)[0] (-1)[1] Q ≈ M`, a signed permutation.",
    chain=[P("H02 Z0 H02 H13 Z1 H13"), P("Z0 Z2 X02 H02 H02 H13 Z1 H13"),
           P("Z0 Z2 X02 Z1 Z3 X13 H13 H13"), P("Z0 Z2 X02 Z1 Z3 X13")], maxd=6)
add("ma", 4, M + A, B + M, "`M H[0,1] ≈ H[2,3] M`.", maxd=10, maxlen=12)
add("mswap4", 4, M, P("X02 X13 Z0 Z1 Z2 Z3"), "The signed permutation `M` in two orders.",
    chain=[P("Z0 Z1 Z2 X02 Z3 X13"), P("Z0 Z1 Z2 X02 X13 Z1"), P("Z0 Z2 X02 Z1 X13 Z1"),
           P("Z0 Z2 X02 X13 Z3 Z1"), P("Z0 X02 Z0 X13 Z3 Z1"), P("X02 Z2 Z0 X13 Z3 Z1"),
           P("X02 X13 Z2 Z0 Z3 Z1")], maxd=5)
add("mm4", 4, M + M, (), "`M M ≈ ε`.", chain=[M + P("X02 X13 Z0 Z1 Z2 Z3"),
    P("Z0 Z1 Z2 Z3 X02 X02 X13 X13 Z0 Z1 Z2 Z3"), P("Z0 Z1 Z2 Z3 Z0 Z1 Z2 Z3")], maxd=6)
add("qm", 4, Q + M, Zs + Q, "`Q M ≈ (-1)[0] (-1)[1] Q`.", chain=[Q + Q + Zs + Q], maxd=5)
add("e1", 4, A + Q + A + Q, Q + A + Q + B,
    "Clément's (20) as `A Q A Q ≈ Q A Q B`, `A = H[0,1]`, `B = H[2,3]`, `Q = H[0,2] H[1,3]`.",
    full=True, maxd=5,
    chain=[A + Q + A + Q + M + M, A + Q + A + Zs + Q + M, Q + A + Zs + Q + A + M,
           Q + A + Q + M + A + M, Q + A + Q + B + M + M])
add("qb", 4, Q + B, B + A + Q + A, "`Q B ≈ B A Q A`, by (19) (that is (f1)).", maxd=6, maxlen=10)
add("e1pp", 4, Q + B + Q + B + A, B + Q + B + Q + B, "`Q B Q B A ≈ B Q B Q B`, by (20) and (19).",
    full=True, maxd=6, maxlen=14,
    chain=[B + A + Q + A + B + A + Q + A + A, B + A + Q + B + Q, B + A + B + A + Q + A + Q, Q + A + Q,
           Q + A + Q + B + B, A + Q + A + Q + B, B + B + A + Q + A + Q + B])
add("d3", 4, (B + Q) * 4, A + B,
    "Figure 6's (d3) at `0, 1, 2, 3`: `(H[2,3] H[0,2] H[1,3])⁴ ≈ H[0,1] H[2,3]`.",
    full=True, maxd=5,
    chain=[(B + Q) * 4 + B + B, B + Q + B + Q + Q + B + Q + B + A + B, B + Q + B + B + Q + B + A + B,
           B + Q + Q + B + A + B, B + B + A + B])

# ---- six indices ----
add("zv4", 4, P("Z0 Z1 Z2 Z3 H02 H13"), P("H02 H13 Z0 Z1 Z2 Z3"), "Signs on all four indices pass `Q`.",
    chain=[P("Z1 Z3 Z0 Z2 H02 H13"), P("Z1 Z3 H02 Z0 Z2 H13"), P("H02 Z1 Z3 H13 Z0 Z2"),
           P("H02 H13 Z1 Z3 Z0 Z2")], maxd=5)
add("zc4", 4, P("Z0 Z1 Z2 Z3 H23"), P("H23 Z0 Z1 Z2 Z3"), "Signs on all four indices pass `H[2,3]`.",
    chain=[P("Z0 Z1 H23 Z2 Z3")], maxd=5)
add("mbm", 4, A, M + B + M, "`A ≈ M B M`.", chain=[M + M + A], maxd=4)
add("mq", 4, M + Q, Q + Zs, "`M Q ≈ Q (-1)[0] (-1)[1]`.", chain=[Q + Zs + Q + Q], maxd=5)
add("qaqz", 4, Q + A + Q, Zs + Q + B + Q + Zs, "`Q A Q ≈ Z Q B Q Z` with `Z = (-1)[0] (-1)[1]`.",
    chain=[Q + M + B + M + Q, Zs + Q + B + M + Q], maxd=6)
Q6 = P("H02 H13"); R6 = P("H04 H15"); A6 = P("H01"); V6 = P("H24 H35"); C6 = P("H45")
B6 = P("H23"); X6 = P("X24 X35"); Z6 = P("Z0 Z1"); Z23 = P("Z2 Z3"); Z45 = P("Z4 Z5")
Z2345 = P("Z2 Z3 Z4 Z5"); M6 = P("Z0 Z1 Z4 Z5 X04 X15")
T6 = Q6 + A6 + Q6; T6p = R6 + A6 + R6
add("conjX", 6, X6 + T6 + X6, T6p, "`X T X ≈ T'`, `T = Q A Q`, `T' = R A R`, `X = X[2,4] X[3,5]`.",
    chain=[R6 + X6 + A6 + Q6 + X6, R6 + A6 + X6 + Q6 + X6, R6 + A6 + R6 + X6 + X6], maxd=6)
add("conjX2", 6, X6 + T6p + X6, T6, "`X T' X ≈ T`.", chain=[X6 + X6 + T6 + X6 + X6], maxd=6)
add("xhx", 2, P("X01 H01 X01"), P("Z0 H01 Z1"), "`X[0,1] H[0,1] X[0,1] ≈ (-1)[0] H[0,1] (-1)[1]`.",
    maxd=8, maxlen=8)
add("xvx", 6, X6 + V6 + X6, Z23 + V6 + Z45, "`X V X ≈ (-1)[2] (-1)[3] V (-1)[4] (-1)[5]`.",
    chain=[P("X24 H24 X24 X35 H35 X35"), P("Z2 H24 Z4 Z3 H35 Z5")], maxd=6)
add("xcx", 6, X6 + C6 + X6, B6, "`X C X ≈ H[2,3]`.", maxd=8, maxlen=10)
add("xvcvx", 6, X6 + V6 + C6 + V6 + X6, V6 + C6 + V6, "`X` commutes with `V C V`.",
    chain=[X6 + V6 + X6 + X6 + C6 + X6 + X6 + V6 + X6, Z23 + V6 + Z45 + B6 + Z23 + V6 + Z45,
           Z23 + V6 + B6 + Z2345 + V6 + Z45, Z23 + V6 + B6 + V6 + Z2345 + Z45, Z23 + V6 + B6 + V6 + Z23,
           Z23 + Z23 + V6 + C6 + V6 + Z23 + Z23], maxd=6)
add("mswap", 6, M6, P("X04 X15 Z0 Z1 Z4 Z5"), "The signed permutation `M'` in two orders.",
    chain=[P("Z0 Z1 Z4 X04 Z5 X15"), P("Z0 Z1 Z4 X04 X15 Z1"), P("Z0 Z4 X04 Z1 X15 Z1"),
           P("Z0 Z4 X04 X15 Z5 Z1"), P("Z0 X04 Z0 X15 Z5 Z1"), P("X04 Z4 Z0 X15 Z5 Z1"),
           P("X04 X15 Z4 Z0 Z5 Z1")], maxd=5)
add("mm6", 6, M6 + M6, (), "`M' M' ≈ ε`.", chain=[M6 + P("X04 X15 Z0 Z1 Z4 Z5"),
    P("Z0 Z1 Z4 Z5 X04 X04 X15 X15 Z0 Z1 Z4 Z5"), P("Z0 Z1 Z4 Z5 Z0 Z1 Z4 Z5"),
    P("Z0 Z0 Z1 Z1 Z4 Z4 Z5 Z5")], maxd=4)
add("rzr", 6, R6 + Z6 + R6, M6, "`R (-1)[0] (-1)[1] R ≈ M'`.",
    chain=[P("H04 Z0 H04 H15 Z1 H15"), P("Z0 Z4 X04 H04 H04 H15 Z1 H15"),
           P("Z0 Z4 X04 Z1 Z5 X15 H15 H15"), P("Z0 Z4 X04 Z1 Z5 X15")], maxd=6)
add("zhz", 2, P("Z0 H01 Z0"), P("Z1 X01 H01"), "`(-1)[0] H[0,1] (-1)[0] ≈ (-1)[1] X[0,1] H[0,1]`.",
    maxd=6)
add("rev3", 3, P("X02 H01 X02"), P("X12 H12 X12"), "`X[0,2] H[0,1] X[0,2] ≈ X[1,2] H[1,2] X[1,2]`.",
    maxd=8, maxlen=10)
add("rm", 6, R6 + M6, Z6 + R6, "`R M' ≈ (-1)[0] (-1)[1] R`.", chain=[R6 + R6 + Z6 + R6], maxd=5)
add("mqm", 6, M6 + Q6 + M6, Z2345 + V6, "`M' Q M' ≈ (-1)[2] ⋯ (-1)[5] V`.",
    chain=[P("Z0 Z1 Z4 Z5 X04 X15 H02 H13 X04 X15 Z0 Z1 Z4 Z5"),
           P("Z0 Z1 Z4 Z5 X04 H02 X04 X15 H13 X15 Z0 Z1 Z4 Z5"),
           P("Z0 Z1 Z4 Z5 X24 H24 X24 X35 H35 X35 Z0 Z1 Z4 Z5"),
           P("Z4 Z5 X24 H24 X24 X35 H35 X35 Z0 Z1 Z0 Z1 Z4 Z5"),
           P("Z4 Z5 X24 H24 X24 X35 H35 X35 Z4 Z5"),
           P("Z4 X24 H24 X24 Z4 Z5 X35 H35 X35 Z5"),
           P("X24 Z2 H24 Z2 X24 Z5 X35 H35 X35 Z5"),
           P("X24 Z2 H24 Z2 X24 X35 Z3 H35 Z3 X35"),
           P("X24 Z4 X24 H24 X24 X35 Z5 X35 H35 X35"),
           P("Z2 H24 X24 Z3 H35 X35"), P("Z2 Z4 H24 Z3 Z5 H35")], maxd=6)
add("ma6", 6, M6 + A6, C6 + M6, "`M' H[0,1] ≈ H[4,5] M'`.", maxd=8, maxlen=12)
add("mtm", 6, M6 + T6 + M6, V6 + C6 + V6, "`M' T M' ≈ V C V`.",
    chain=[M6 + Q6 + M6 + M6 + A6 + M6 + M6 + Q6 + M6, Z2345 + V6 + M6 + A6 + M6 + Z2345 + V6,
           Z2345 + V6 + C6 + M6 + M6 + Z2345 + V6, Z2345 + V6 + C6 + Z2345 + V6,
           V6 + Z2345 + C6 + Z2345 + V6, V6 + C6 + Z2345 + Z2345 + V6], maxd=6)
L21 = A6 + Q6 + R6 + A6 + Z6 + R6 + Q6
R21 = Q6 + R6 + A6 + Z6 + R6 + Q6 + A6
add("braid", 6, T6p + T6 + T6p, M6 + T6 + M6,
    "Clément's (21) as `T' T T' ≈ M' T M'`, with `R = H[0,4] H[1,5]`, `M' = R (-1)[0] (-1)[1] R`.",
    full=True, maxd=5,
    chain=[T6p + T6 + T6p + M6 + M6, T6p + Q6 + Q6 + T6 + T6p + M6 + M6,
           T6p + Q6 + Q6 + T6 + T6p + M6 + Q6 + Q6 + M6,
           T6p + Q6 + A6 + Q6 + R6 + A6 + R6 + M6 + Q6 + Q6 + M6,
           T6p + Q6 + L21 + Q6 + M6, T6p + Q6 + R21 + Q6 + M6,
           T6p + R6 + A6 + Z6 + R6 + Q6 + A6 + Q6 + M6,
           T6p + R6 + A6 + R6 + M6 + Q6 + A6 + Q6 + M6])
add("d4f", 6, T6 + T6p + T6, V6 + C6 + V6, "`T T' T ≈ V C V`, `V = H[2,4] H[3,5]`, `C = H[4,5]`.",
    full=True, maxd=6,
    chain=[X6 + T6p + X6 + X6 + T6 + X6 + X6 + T6p + X6, X6 + T6p + T6 + T6p + X6, X6 + M6 + T6 + M6 + X6,
           X6 + V6 + C6 + V6 + X6])
add("d4", 6, (T6 + X6) * 3, V6 + C6 + V6 + X6,
    "Figure 6's (d4) at `0, …, 5`: `(H[0,2] H[1,3] H[0,1] H[0,2] H[1,3] X[2,4] X[3,5])³ ≈ "
    "H[2,4] H[3,5] H[4,5] H[2,4] H[3,5] X[2,4] X[3,5]`.",
    full=True, maxd=6, chain=[T6 + X6 + T6 + X6 + T6 + X6, T6 + T6p + T6 + X6])

header = """/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Figure 6's (d3) and (d4) from Clément's relations

Generated by `gen/gen_derivedc.py` (run `python gen_derivedc.py ../DerivedC.lean`
in `gen/`); do not edit by hand.

With `A = H[0,1]`, `B = H[2,3]`, `Q = H[0,2] H[1,3]` and the signed
permutation `M = Q (-1)[0] (-1)[1] Q` (`kqzq`), which carries `A` to `B`
(`kma`): Clément's (20), `A Q A Z Q ≈ Q A Z Q A`, is `A Q A Q ≈ Q A Q B`
(`ke1`).  With (19) (which is Hadamard-Π's (f1), `Q B ≈ B A Q A`, `kqb`) this
gives `Q B Q B A ≈ B Q B Q B` (`ke1pp`): both sides are `Q A Q`.  Hence
`(B Q)⁴ ≈ (B Q B Q)(Q B Q B A B) ≈ A B`, which is (d3) (`kd3`).

On six indices, with `T = Q A Q`, `T' = R A R`, `R = H[0,4] H[1,5]`,
`V = H[2,4] H[3,5]`, `C = H[4,5]`, `X = X[2,4] X[3,5]` and
`M' = R (-1)[0] (-1)[1] R`: Clément's (21) says that `A` commutes with
`Q T' M' Q`, that is `T' T T' ≈ M' T M'` (`kbraid`); `M' T M' ≈ V C V`
(`kmtm`) and `X` conjugates `T` to `T'` (`kconjX`) and commutes with `V C V`
(`kxvcvx`), so `T T' T ≈ X (T' T T') X ≈ V C V` (`kd4f`), and
`(T X)³ ≈ T T' T X ≈ V C V X`, which is (d4) (`kd4`).
-/
import QCert.Clement2019.CheckC

namespace QCert.Clement2019

open FreeMonoid

"""
open(sys.argv[1], "w", encoding="utf-8", newline="\n").write(
    header + lib.text() + "\nend QCert.Clement2019\n")
print("written", sys.argv[1])
