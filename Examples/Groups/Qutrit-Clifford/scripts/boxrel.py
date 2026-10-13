"""The box relations of Appendix C, transcribed in time order.

Two-wire figures: top = wire 1, bottom = wire 0.  Three-wire: top 2, middle 1,
bottom 0.  Each relation is (figure, name, width, lhs, rhs).
"""
from qt import *
from boxes import A, B, C, D, E, F

def Hk(w, k): return H(w) * (k % 4)
def Sk(w, k): return S(w) * (k % 3)
def Xk(w, k): return X(w) * (k % 3)
def Zk(w, k): return Z(w) * (k % 3)
def CZk(w, k): return CZ(w) * (k % 3)

def ph(sign, k):
    """sign * omega^k as a power of nu = -omega."""
    e = (4 * k + (3 if sign < 0 else 0)) % 6
    return nu(e)

OM = lambda k: ph(1, k)       # omega^k
MOM = lambda k: ph(-1, k)     # -omega^k

R = []
def rel(fig, name, n, l, r):
    R.append((fig, name, n, l, r))

Z3 = range(3)
nz = [(a, b) for a in Z3 for b in Z3 if (a, b) != (0, 0)]

# ---------------------------------------------------------------- one qutrit
for (a, b) in nz:
    r = A(b, (2 * a) % 3)
    if a * b == 0:
        pass
    elif a == b:
        r = r + Sk(0, 2) + Xk(0, 2) + MOM(2)
    else:
        r = r + X(0) + S(0) + MOM(1)
    rel(18, f'H.A{a}{b}', 1, H(0) + A(a, b), r)

rel(19, 'S.A01', 1, S(0) + A(0, 1), A(0, 1) + S(0))
rel(19, 'S.A02', 1, S(0) + A(0, 2), A(0, 2) + S(0) + Zk(0, 2))
for b in Z3:
    rel(19, f'S.A1{b}', 1, S(0) + A(1, b), A(1, (b + 1) % 3))
    rel(19, f'S.A2{b}', 1, S(0) + A(2, b), A(2, (b + 2) % 3) + X(0))

for b in Z3:
    rel(20, f'S.C{b}', 1, S(0) + C(b), C(b) + S(0) + Zk(0, b) + OM(b * (b + 1)))
    rel(20, f'Z.C{b}', 1, Z(0) + C(b), C(b) + Z(0) + OM(2 * b))
    rel(20, f'X.C{b}', 1, X(0) + C(b), C((b + 1) % 3))
    rel(21, f'S.E{b}', 1, S(0) + E(b), E((b + 1) % 3))
    rel(21, f'Z.E{b}', 1, Z(0) + E(b), E(b) + Z(0))
    rel(22, f'Z.F{b}', 1, Z(0) + F(b), F((b + 2) % 3))

# ---------------------------------------------------------------- two qutrits
T, Bo = 1, 0
for c in (1, 2):
    rel(23, f'CZ.A0{c}', 2, CZ() + A(0, c, T), A(0, c, T) + CZk(0, c))
for b in Z3:
    rel(23, f'CZ.A1{b}', 2, CZ() + A(1, b, T),
        A(0, 2, Bo) + B(1, b) + S(T) + Sk(Bo, 2) + H(Bo) + CZk(0, 2) + H(Bo) + Sk(Bo, 2) + Hk(Bo, 2) + OM(1))
    rel(23, f'CZ.A2{b}', 2, CZ() + A(2, b, T),
        A(0, 1, Bo) + B(2, b) + S(T) + Sk(Bo, 2) + H(Bo) + CZk(0, 2) + H(Bo) + Sk(Bo, 2) + OM(1))

# Figure 24: CZ, A01 (bottom), B.
L = lambda a, b, ab, bb: CZ() + A(a, b, Bo) + B(ab, bb)
rel(24, 'CZ.A01.B00', 2, L(0, 1, 0, 0), A(0, 1, Bo) + B(0, 0) + CZ())
rel(24, 'CZ.A01.B01', 2, L(0, 1, 0, 1), A(0, 1, Bo) + B(0, 1) + CZ() + Hk(Bo, 2) + S(Bo) + Hk(Bo, 2) + S(Bo) + OM(1))
rel(24, 'CZ.A01.B02', 2, L(0, 1, 0, 2), A(0, 1, Bo) + B(0, 2) + CZk(0, 2) + S(Bo) + Hk(Bo, 2) + Sk(Bo, 2) + Hk(Bo, 2) + S(Bo) + OM(2))
for b in Z3:
    rel(24, f'CZ.A01.B1{b}', 2, L(0, 1, 1, b),
        A(1, b, T) + Sk(T, 2) + S(Bo) + H(Bo) + CZk(0, 2) + H(Bo) + S(Bo) + OM(2))
    rel(24, f'CZ.A01.B2{b}', 2, L(0, 1, 2, b),
        A(0, 2, Bo) + B(2, b) + S(Bo) + Hk(Bo, 2) + S(Bo) + H(Bo) + CZk(0, 2)
        + Hk(Bo, 3) + S(Bo) + Hk(Bo, 2) + Sk(Bo, 2) + Hk(Bo, 2) + S(Bo))

# Figure 25: CZ, A02, B.
rel(25, 'CZ.A02.B00', 2, L(0, 2, 0, 0), A(0, 2, Bo) + B(0, 0) + CZk(0, 2))
rel(25, 'CZ.A02.B01', 2, L(0, 2, 0, 1), A(0, 2, Bo) + B(0, 1) + CZk(0, 2) + Hk(Bo, 2) + Sk(Bo, 2) + Hk(Bo, 2) + Sk(Bo, 2) + OM(2))
rel(25, 'CZ.A02.B02', 2, L(0, 2, 0, 2), A(0, 2, Bo) + B(0, 2) + CZ() +  # misprint: the paper has CZ CZ
    Sk(Bo, 2) + Hk(Bo, 2) + S(Bo) + Hk(Bo, 2) + Sk(Bo, 2) + OM(1))
for b in Z3:
    rel(25, f'CZ.A02.B1{b}', 2, L(0, 2, 1, b),
        A(0, 1, Bo) + B(1, b) + S(Bo) + Hk(Bo, 2) + S(Bo) + H(Bo) + CZk(0, 2)
        + Hk(Bo, 3) + S(Bo) + Hk(Bo, 2) + Sk(Bo, 2) + Hk(Bo, 2) + S(Bo))
    rel(25, f'CZ.A02.B2{b}', 2, L(0, 2, 2, b),
        A(2, b, T) + Sk(T, 2) + Hk(Bo, 2) + S(Bo) + H(Bo) + CZk(0, 2) + H(Bo) + S(Bo) + OM(2))

# Figure 26: CZ, A1b, B.
for b in Z3:
    rel(26, f'CZ.A1{b}.B00', 2, L(1, b, 0, 0), A(1, b, Bo) + B(0, 2) + CZk(0, 2) + Hk(Bo, 2))
    rel(26, f'CZ.A1{b}.B01', 2, L(1, b, 0, 1), A(1, b, Bo) + B(0, 0) + CZ() + Sk(Bo, 2) + Hk(Bo, 2) + Sk(Bo, 2) + Hk(Bo, 2) + OM(2))
    rel(26, f'CZ.A1{b}.B02', 2, L(1, b, 0, 2), A(1, b, Bo) + B(0, 1) + CZ() + S(Bo) + Hk(Bo, 2) + S(Bo) + OM(1))
    for d in Z3:
        rel(26, f'CZ.A1{b}.B1{d}', 2, L(1, b, 1, d),
            A(1, b + 2, Bo) + B(1, (d + 2) % 3) + S(Bo) + H(Bo) + CZk(0, 2)
            + S(T) + Xk(T, 2) + H(Bo) + Sk(Bo, 2) + Hk(Bo, 3) + S(Bo) + Hk(Bo, 2) + MOM(2))
        rel(26, f'CZ.A1{b}.B2{d}', 2, L(1, b, 2, d),
            A(1, b + 1, Bo) + B(2, (d + 2) % 3) + S(T) + X(T) + S(T) + Hk(Bo, 2) + S(Bo) + H(Bo)
            + CZk(0, 2) + Sk(Bo, 2) + Hk(Bo, 3) + S(Bo) + Hk(Bo, 2) + S(Bo) + OM(1))

# Figure 27: CZ, A2b, B.
for b in Z3:
    rel(27, f'CZ.A2{b}.B00', 2, L(2, b, 0, 0), A(2, b, Bo) + B(0, 1) + CZk(0, 2) + Sk(Bo, 2) + Hk(Bo, 2) + S(Bo) + Hk(Bo, 2) + Sk(Bo, 2) + OM(1))
    rel(27, f'CZ.A2{b}.B01', 2, L(2, b, 0, 1), A(2, b, Bo) + B(0, 2) + CZ() + Sk(Bo, 2) + Hk(Bo, 2) + Sk(Bo, 2) + OM(2))
    rel(27, f'CZ.A2{b}.B02', 2, L(2, b, 0, 2), A(2, b, Bo) + B(0, 0) + CZk(0, 2) + Hk(Bo, 2))
    for d in Z3:
        rel(27, f'CZ.A2{b}.B1{d}', 2, L(2, b, 1, d),
            A(2, b + 2, Bo) + B(1, (d + 1) % 3) + S(T) + X(T) + S(T) + Hk(Bo, 2) + S(Bo) + H(Bo)
            + CZk(0, 2) + Sk(Bo, 2) + Hk(Bo, 3) + S(Bo) + Hk(Bo, 2) + S(Bo) + OM(1))
        rel(27, f'CZ.A2{b}.B2{d}', 2, L(2, b, 2, d),
            A(2, b + 1, Bo) + B(2, (d + 1) % 3) + S(Bo) + H(Bo) + CZk(0, 2)
            + S(T) + Xk(T, 2) + H(Bo) + Sk(Bo, 2) + Hk(Bo, 3) + S(Bo) + Hk(Bo, 2) + MOM(2))

# Figure 28: H (top) through B.
rel(28, 'HxI.B00', 2, H(T) + B(0, 0), B(0, 0) + CZk(0, 2) + H(Bo) + CZ())
rel(28, 'HxI.B01', 2, H(T) + B(0, 1), B(1, 0) + CZ() + S(Bo) + Hk(Bo, 2) + S(Bo) + Hk(Bo, 2) + OM(1))
rel(28, 'HxI.B02', 2, H(T) + B(0, 2), B(2, 0) + CZk(0, 2) + Sk(Bo, 2) + Hk(Bo, 2) + Sk(Bo, 2) + Hk(Bo, 2) + OM(2))
rel(28, 'HxI.B10', 2, H(T) + B(1, 0), B(0, 2) + CZ() + S(Bo) + Hk(Bo, 2) + S(Bo) + Hk(Bo, 2) + OM(1))
TAIL2 = lambda: Sk(Bo, 2) + H(Bo) + Sk(Bo, 2) + Hk(Bo, 2) + S(Bo) + Hk(Bo, 3) + Sk(Bo, 2) + Hk(Bo, 2) + S(Bo)
TAIL1 = lambda: S(Bo) + H(Bo) + S(Bo) + Hk(Bo, 2) + Sk(Bo, 2) + Hk(Bo, 3) + Sk(Bo, 2) + Hk(Bo, 2) + S(Bo)
rel(28, 'HxI.B11', 2, H(T) + B(1, 1), B(1, 2) + Xk(T, 2) + Zk(T, 2) + TAIL2() + MOM(2))
rel(28, 'HxI.B12', 2, H(T) + B(1, 2), B(2, 2) + X(T) + Z(T) + TAIL1() + MOM(2))
rel(28, 'HxI.B20', 2, H(T) + B(2, 0), B(0, 1) + CZk(0, 2) + Sk(Bo, 2) + Hk(Bo, 2) + Sk(Bo, 2) + Hk(Bo, 2) + OM(2))
rel(28, 'HxI.B21', 2, H(T) + B(2, 1), B(1, 1) + X(T) + Z(T) + TAIL1() + MOM(2))
rel(28, 'HxI.B22', 2, H(T) + B(2, 2), B(2, 1) + Xk(T, 2) + Zk(T, 2) + TAIL2() + MOM(2))

# Figure 29: S (top) through B.
rel(29, 'SxI.B00', 2, S(T) + B(0, 0), B(0, 0) + S(Bo))
rel(29, 'SxI.B01', 2, S(T) + B(0, 1), B(0, 1) + S(Bo))
rel(29, 'SxI.B02', 2, S(T) + B(0, 2), B(0, 2) + Hk(Bo, 2) + S(Bo) + Hk(Bo, 2))
for b in Z3:
    rel(29, f'SxI.B1{b}', 2, S(T) + B(1, b), B(1, (b + 1) % 3))
    rel(29, f'SxI.B2{b}', 2, S(T) + B(2, b),
        B(2, (b + 2) % 3) + X(T) + Z(T) + H(Bo) + S(Bo) + Hk(Bo, 2) + Sk(Bo, 2) + Hk(Bo, 3) + S(Bo) + Hk(Bo, 2) + Sk(Bo, 2))

# Figures 30-32: S, X, Z (bottom) through B.
rel(30, 'IxS.B00', 2, S(Bo) + B(0, 0), B(0, 0) + S(T))
rel(31, 'IxX.B00', 2, X(Bo) + B(0, 0), B(0, 0) + X(T) + Hk(Bo, 2) + Sk(Bo, 2) + Hk(Bo, 2) + S(Bo))
rel(31, 'IxX.B01', 2, X(Bo) + B(0, 1), B(0, 1) + X(T) + Hk(Bo, 2) + S(Bo) + Hk(Bo, 2) + Sk(Bo, 2))
rel(31, 'IxX.B02', 2, X(Bo) + B(0, 2), B(0, 2) + X(T))
rel(32, 'IxZ.B00', 2, Z(Bo) + B(0, 0), B(0, 0) + Z(T))
for (a, b) in nz:
    rel(30, f'IxS.B{a}{b}', 2, S(Bo) + B(a, b), B(a, b) + CZ() + S(T) + Hk(Bo, 2) + S(Bo) + Hk(Bo, 2) + OM(2))
    rel(32, f'IxZ.B{a}{b}', 2, Z(Bo) + B(a, b), B(a, b) + Z(T) + Hk(Bo, 2) + S(Bo) + Hk(Bo, 2) + Sk(Bo, 2))
    if a != 0:
        rel(31, f'IxX.B{a}{b}', 2, X(Bo) + B(a, b), B(a, b) + X(T) + Hk(Bo, 2) + Sk(Bo, 2) + Hk(Bo, 2) + S(Bo))

# Figure 33: CZ through C (C on top).
rel(33, 'CZ.C0', 2, CZ() + C(0, T), C(0, T) + CZ())
rel(33, 'CZ.C1', 2, CZ() + C(1, T), C(1, T) + CZ() + Hk(Bo, 2) + S(Bo) + Hk(Bo, 2) + Sk(Bo, 2))
rel(33, 'CZ.C2', 2, CZ() + C(2, T), C(2, T) + CZ() + Hk(Bo, 2) + Sk(Bo, 2) + Hk(Bo, 2) + S(Bo))

# Figure 34: H (bottom) through D.
rel(34, 'IxH.D00', 2, H(Bo) + D(0, 0), D(0, 0) + H(T))
rel(34, 'IxH.D01', 2, H(Bo) + D(0, 1), D(1, 0))
rel(34, 'IxH.D02', 2, H(Bo) + D(0, 2), D(2, 0) + Hk(T, 2))
rel(34, 'IxH.D10', 2, H(Bo) + D(1, 0), D(0, 2) + Hk(T, 2))
rel(34, 'IxH.D11', 2, H(Bo) + D(1, 1), D(1, 2) + Sk(T, 2) + H(T) + Sk(T, 2) + Hk(T, 2) + S(T) + H(T) + Z(Bo) + MOM(2))
rel(34, 'IxH.D12', 2, H(Bo) + D(1, 2), D(2, 2) + Hk(T, 2) + S(T) + Hk(T, 3) + S(T) + Hk(T, 2) + Sk(T, 2) + H(T) + Zk(Bo, 2) + MOM(1))
rel(34, 'IxH.D20', 2, H(Bo) + D(2, 0), D(0, 1))
rel(34, 'IxH.D21', 2, H(Bo) + D(2, 1), D(1, 1) + Hk(T, 2) + S(T) + Hk(T, 3) + S(T) + Hk(T, 2) + Sk(T, 2) + H(T) + Zk(Bo, 2) + MOM(1))
rel(34, 'IxH.D22', 2, H(Bo) + D(2, 2), D(2, 1) + Sk(T, 2) + H(T) + Sk(T, 2) + Hk(T, 2) + S(T) + H(T) + Z(Bo) + MOM(2))

# Figures 35-37.
for b in Z3:
    rel(35, f'IxS.D0{b}', 2, S(Bo) + D(0, b), D(0, b) + S(T))
    rel(35, f'IxS.D1{b}', 2, S(Bo) + D(1, b), D(1, (b + 1) % 3))
    rel(35, f'IxS.D2{b}', 2, S(Bo) + D(2, b), D(2, (b + 2) % 3) + H(T) + S(T) + Hk(T, 2) + Sk(T, 2) + H(T) + Zk(Bo, 2))
    rel(37, f'CZ.D0{b}', 2, CZ() + D(0, b), D(0, (b + 2) % 3))
    rel(37, f'CZ.D1{b}', 2, CZ() + D(1, b), D(1, (b + 2) % 3) + Hk(T, 3) + S(T) + H(T) + Sk(Bo, 2) + Z(Bo) + OM(1))
    rel(37, f'CZ.D2{b}', 2, CZ() + D(2, b), D(2, (b + 2) % 3) + Hk(T, 3) + Sk(T, 2) + H(T) + S(Bo) + Zk(Bo, 2) + OM(2))
for a in Z3:
    for b in Z3:
        rel(36, f'SxI.D{a}{b}', 2, S(T) + D(a, b), D(a, b) + S(Bo))
        rel(36, f'ZxI.D{a}{b}', 2, Z(T) + D(a, b), D(a, b) + Z(Bo))

# ---------------------------------------------------------------- three qutrits
# Figures 38-42: CZ on wires (2,1), B on (1,0), then B on (2,1).
LL = lambda a, b, c, d: CZ(1) + B(a, b, 0) + B(c, d, 1)
def bb(a, b, c, d, a2, b2, c2, d2, tail):
    rel(38 + {(0, 0): 0, (0, 1): 1, (0, 2): 2}.get((a, b), 3 if a == 1 else 4),
        f'CZ.B{a}{b}.B{c}{d}', 3, LL(a, b, c, d), B(a2, b2, 0) + B(c2, d2, 1) + tail)

# Figure 38: first box B00.
bb(0, 0, 0, 0, 0, 0, 0, 0, CZ(0))
bb(0, 0, 0, 1, 0, 0, 0, 1, CZ(0))
bb(0, 0, 0, 2, 0, 0, 0, 2, CZk(0, 2))
for b in Z3:
    bb(0, 0, 1, b, 0, 2, 1, b, H(1) + S(1) + H(1) + Hk(0, 2) + Sk(0, 2) + CZk(0, 2) + Hk(1, 3) + Sk(1, 2) + Hk(1, 3) + OM(1))
    bb(0, 0, 2, b, 0, 1, 2, b, Hk(1, 3) + S(1) + H(1) + Sk(0, 2) + CZk(0, 2) + Hk(1, 3) + Sk(1, 2) + H(1) + OM(1))
# Figure 39: first box B01.
bb(0, 1, 0, 0, 0, 1, 0, 0, CZ(0))
bb(0, 1, 0, 1, 0, 1, 0, 1, CZ(0))
bb(0, 1, 0, 2, 0, 1, 0, 2, CZk(0, 2))
for b in Z3:
    bb(0, 1, 1, b, 0, 0, 1, b, Sk(1, 2) + H(1) + S(0) + CZk(0, 2) + Hk(1, 3) + S(1) + OM(2))
    bb(0, 1, 2, b, 0, 2, 2, b, Hk(1, 3) + S(1) + H(1) + CZ(0) + Hk(1, 3) + Sk(1, 2) + H(1) + Sk(0, 2) + Hk(0, 2) + S(0))
# Figure 40: first box B02.
bb(0, 2, 0, 0, 0, 2, 0, 0, CZk(0, 2))
bb(0, 2, 0, 1, 0, 2, 0, 1, CZk(0, 2))
bb(0, 2, 0, 2, 0, 2, 0, 2, CZ(0))
for b in Z3:
    bb(0, 2, 1, b, 0, 1, 1, b, Hk(1, 3) + S(1) + H(1) + CZ(0) + Hk(1, 3) + Sk(1, 2) + H(1) + Sk(0, 2) + Hk(0, 2) + S(0))
    bb(0, 2, 2, b, 0, 0, 2, b, Sk(1, 2) + H(1) + CZ(0) + Hk(1, 3) + S(1) + Hk(0, 2) + S(0) + OM(2))
# Figure 41: first box B1b.
for b in Z3:
    bb(1, b, 0, 0, 1, b, 0, 2, Hk(1, 2) + S(1) + Sk(0, 2) + H(0) + CZk(0, 2) + Hk(0, 3) + S(0) + OM(2))
    bb(1, b, 0, 1, 1, b, 0, 0, Hk(1, 2) + S(1) + Hk(1, 2) + Sk(1, 2) + Sk(0, 2) + H(0) + CZk(0, 2) + Hk(0, 3) + S(0))
    bb(1, b, 0, 2, 1, b, 0, 1, Hk(1, 2) + Sk(1, 2) + Hk(0, 2) + Sk(0, 2) + H(0) + CZk(0, 2)
       + Hk(1, 2) + Sk(1, 2) + Hk(1, 2) + S(1) + Hk(0, 3) + S(0) + Hk(0, 2) + OM(1))
    for d in Z3:
        bb(1, b, 1, d, 1, (b + 2) % 3, 1, (d + 2) % 3,
           Xk(2, 2) + Zk(2, 2) + Sk(1, 2) + H(1) + Sk(0, 2) + H(0) + CZ(0)
           + Hk(1, 3) + Sk(1, 2) + H(1) + Sk(1, 2) + Hk(1, 2) + S(1)
           + Hk(0, 3) + Sk(0, 2) + H(0) + Sk(0, 2) + Hk(0, 2) + S(0) + OM(1))
        bb(1, b, 2, d, 1, (b + 1) % 3, 2, (d + 2) % 3,
           X(2) + Z(2) + Hk(1, 2) + Sk(1, 2) + H(1) + Hk(0, 2) + Sk(0, 2) + H(0) + CZk(0, 2)
           + Sk(1, 2) + Hk(1, 3) + S(1) + Hk(1, 2) + Sk(0, 2) + Hk(0, 3) + S(0) + Hk(0, 2))
# Figure 42: first box B2b.
for b in Z3:
    bb(2, b, 0, 0, 2, b, 0, 1, S(0) + Hk(0, 2) + S(0) + H(0) + CZk(0, 2) + H(0) + Sk(0, 2) + Hk(0, 2) + Sk(0, 2) + Hk(0, 2))
    bb(2, b, 0, 1, 2, b, 0, 2, Hk(1, 2) + S(1) + Hk(0, 2) + Sk(0, 2) + H(0) + CZk(0, 2) + Hk(0, 3) + S(0) + Hk(0, 2) + OM(2))
    bb(2, b, 0, 2, 2, b, 0, 0, Hk(1, 2) + Sk(1, 2) + Sk(0, 2) + H(0) + CZk(0, 2)
       + Hk(1, 2) + Sk(1, 2) + Hk(1, 2) + S(1) + Hk(0, 3) + S(0) + OM(1))
    for d in Z3:
        bb(2, b, 1, d, 2, (b + 2) % 3, 1, (d + 1) % 3,
           X(2) + Z(2) + Hk(1, 2) + Sk(1, 2) + H(1) + Hk(0, 2) + Sk(0, 2) + H(0) + CZk(0, 2)
           + Sk(1, 2) + Hk(1, 3) + S(1) + Hk(1, 2) + Sk(0, 2) + Hk(0, 3) + S(0) + Hk(0, 2))
        bb(2, b, 2, d, 2, (b + 1) % 3, 2, (d + 1) % 3,
           Xk(2, 2) + Zk(2, 2) + Sk(1, 2) + H(1) + Sk(0, 2) + H(0) + CZ(0)
           + Hk(1, 3) + Sk(1, 2) + H(1) + Sk(1, 2) + Hk(1, 2) + S(1)
           + Hk(0, 3) + Sk(0, 2) + H(0) + Sk(0, 2) + Hk(0, 2) + S(0) + OM(1))

# Figure 43: CZ on (1,0) straddling B on (2,1).
STR = CZ(1) + H(1) + CZk(0, 2) + H(1) + CZ(1) + H(1) + CZk(0, 2) + H(1)
rel(43, 'CZ.B00', 3, CZ(0) + B(0, 0, 1), B(0, 0, 1) + STR)
for (a, b) in nz:
    rel(43, f'CZ.B{a}{b}', 3, CZ(0) + B(a, b, 1), B(a, b, 1) + STR + CZk(0, 2))

# Figure 44: CZ on (1,0), D on (2,1), D on (1,0).
DD = lambda a, b, c, d: CZ(0) + D(a, b, 1) + D(c, d, 0)
for b in Z3:
    for d in Z3:
        rel(44, f'CZ.D0{b}.D0{d}', 3, DD(0, b, 0, d), D(0, b, 1) + D(0, d, 0) + CZ(1))
        rel(44, f'CZ.D0{b}.D1{d}', 3, DD(0, b, 1, d), D(0, (b + 2) % 3, 1) + D(1, d, 0) + H(1) + CZk(1, 2) + Hk(1, 3))
        rel(44, f'CZ.D0{b}.D2{d}', 3, DD(0, b, 2, d), D(0, (b + 1) % 3, 1) + D(2, d, 0) + H(1) + CZ(1) + Hk(1, 3))
        rel(44, f'CZ.D1{b}.D0{d}', 3, DD(1, b, 0, d), D(1, b, 1) + D(0, (d + 2) % 3, 0) + H(2) + CZk(1, 2) + Hk(2, 3))
        rel(44, f'CZ.D1{b}.D1{d}', 3, DD(1, b, 1, d), D(1, (b + 2) % 3, 1) + D(1, (d + 2) % 3, 0)
            + Hk(2, 3) + S(2) + Hk(1, 3) + S(1) + Z(0) + CZ(1) + H(2) + H(1))
        rel(44, f'CZ.D1{b}.D2{d}', 3, DD(1, b, 2, d), D(1, (b + 1) % 3, 1) + D(2, (d + 2) % 3, 0)
            + Hk(2, 3) + Sk(2, 2) + Hk(1, 3) + Sk(1, 2) + Zk(0, 2) + CZk(1, 2) + H(2) + H(1))
        rel(44, f'CZ.D2{b}.D0{d}', 3, DD(2, b, 0, d), D(2, b, 1) + D(0, (d + 1) % 3, 0) + H(2) + CZ(1) + Hk(2, 3))
        rel(44, f'CZ.D2{b}.D1{d}', 3, DD(2, b, 1, d), D(2, (b + 2) % 3, 1) + D(1, (d + 1) % 3, 0)
            + Hk(2, 3) + Sk(2, 2) + Hk(1, 3) + Sk(1, 2) + Zk(0, 2) + CZk(1, 2) + H(2) + H(1))
        rel(44, f'CZ.D2{b}.D2{d}', 3, DD(2, b, 2, d), D(2, (b + 1) % 3, 1) + D(2, (d + 1) % 3, 0)
            + Hk(2, 3) + S(2) + Hk(1, 3) + S(1) + Z(0) + CZ(1) + H(2) + H(1))

if __name__ == '__main__':
    import sys
    bad = 0
    from collections import Counter
    cnt = Counter()
    for fig, name, n, l, r in R:
        cnt[n] += 1
        if not eq(l, r, n):
            bad += 1
            print('FAIL', fig, name)
    print(len(R), 'relations,', bad, 'failures', dict(cnt))
