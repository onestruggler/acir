"""The relations of R1 (Figure 4, Figure 7, (r_K)) read from Syntax.lean."""
import re
from model import *

from paths import module
SYN = module("Syntax.lean")

src = open(SYN, encoding="utf-8").read()

def fig4():
    out = []
    for m in re.finditer(r"\| r(\d+) : Fig4 \(w \[([^\]]*)\]\) \(w \[([^\]]*)\]\)", src):
        n = int(m.group(1))
        l = [s.strip() for s in m.group(2).split(",") if s.strip()]
        r = [s.strip() for s in m.group(3).split(",") if s.strip()]
        out.append((n, l, r))
    return out

FIG4 = fig4()
assert len(FIG4) == 46, len(FIG4)

def fig7():
    x = xab; ng = negw
    R = {
        83: (ng(0) + ng(0), []),
        84: (["Kc", "Kc"], []),
        85: (x(1, 2) + ng(0), ng(0) + x(1, 2)),
        86: (x(2, 3) + ng(0), ng(0) + x(2, 3)),
        87: (x(3, 4) + ng(0), ng(0) + x(3, 4)),
        88: (x(4, 5) + ng(0), ng(0) + x(4, 5)),
        89: (x(5, 6) + ng(0), ng(0) + x(5, 6)),
        90: (x(6, 7) + ng(0), ng(0) + x(6, 7)),
        91: (x(4, 5) + ["Kc"], ["Kc"] + x(4, 5)),
        92: (x(5, 6) + ["Kc"], ["Kc"] + x(5, 6)),
        93: (x(6, 7) + ["Kc"], ["Kc"] + x(6, 7)),
        94: (ng(4) + ["Kc"], ["Kc"] + ng(4)),
        95: (ng(0) + ng(4), ng(4) + ng(0)),
        96: (["Kc"] + kw(4, 5, 6, 7), kw(4, 5, 6, 7) + ["Kc"]),
        97: (x(0, 1) + ["Kc"], ["Kc"] + x(1, 3) + ng(1) + ng(3)),
        98: (x(1, 2) + ["Kc"], ng(0) + ["Kc"] + ng(0) + ["Kc"] + ng(0)),
        99: (x(2, 3) + ["Kc"], ["Kc"] + x(1, 3)),
        100: (["Kc"] + kw(1, 3, 4, 5), kw(2, 3, 4, 5) + kw(0, 1, 2, 4)),
        101: (ng(0) + ng(4) + x(0, 4) + RHO, RHO + x(0, 4) + ng(4) + ng(0)),
    }
    return [(n, l, r) for n, (l, r) in sorted(R.items())]

FIG7 = fig7()
RKRHS = kw(4, 5, 6, 7) + ["X0"] + kw(4, 5, 6, 7) + ["X0"]
RK = ("K", ["K12"], RKRHS)

if __name__ == "__main__":
    for n, l, r in FIG4:
        assert eq(l, r), n
    for n, l, r in FIG7:
        assert eq(l, r), n
    assert eq(RK[1], RK[2])
    print("all sound", len(FIG4), len(FIG7))
    print([ (n, len(l), len(r)) for n, l, r in FIG7])
