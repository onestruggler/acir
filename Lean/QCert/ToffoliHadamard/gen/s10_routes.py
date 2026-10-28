"""Micro routes x -> w_x for the roundTrip, as store entries route_x."""
from paths import work, data, module
import pickle
from store import Store
from asm import Asm
from model import LET, IDX, xAdj, NEG0, kw, eq
from rels import RK
from sat2 import enc_w

S = Store.load(work("store3.pkl"))
# add rK as a base relator
rk_rid = S.R.add(enc_w(RK[1]) + tuple(reversed(enc_w(RK[2]))), "rK")
S.der.append(None)

def I(x): return IDX[x]
def phiL(m):
    if m[0] == 'T': return enc_w(xAdj(m[1]))
    if m == ('N',): return enc_w(NEG0)
    return (I("Kc"),)
def T(i): return ('T', i)
NM, KM = ('N',), ('K',)
def kwM4567():
    from macro import encM, K_
    return [T(x) if x < 7 else (NM if x == 7 else KM) for x in encM(K_(4, 5, 6, 7))]

def w_of(pieces):
    out = []
    for p in pieces:
        out += [I(p[1])] if p[0] == 'L' else list(phiL(p[1]))
    return tuple(out)

def rid(name): return S.find(name)
ROUTES = {}   # x -> pieces

def finish(x, A, pieces):
    w = w_of(pieces)
    assert A.w == w, (x, [LET[c] for c in A.w], [LET[c] for c in w])
    assert eq([x], [LET[c] for c in w]), x
    S.add((I(x),), w, A.steps, f"route_{x}")
    ROUTES[x] = pieces

def M(*ms): return [('M', m) for m in ms]
def L(*ys): return [('L', y) for y in ys]
P = enc_w("X0 X2 CCX01 X0".split()); Pi = enc_w("X0 CCX01 X2 X0".split())
CCX01 = I("CCX01"); X0 = I("X0")

# CCX01, Kc: trivial
A = Asm(S, (CCX01,)); finish("CCX01", A, M(T(6)))
A = Asm(S, (I("Kc"),)); finish("Kc", A, M(KM))
# CCX02 -> T6 T5 T6
A = Asm(S, (I("CCX02"),)); A.ins(0, (CCX01,)); A.ins(3, (CCX01,)); finish("CCX02", A, M(T(6), T(5), T(6)))
# CCX12
A = Asm(S, (I("CCX12"),))
A.fwd(0, rid("m2"))                       # V CCX02 V   (V at 0..2, CCX02 at 3, V at 4..6)
def expandV(A, p):
    A.ins(p, Pi)                          # Pi P V
    A.ins(p + 8 + 3, Pi)                  # Pi P V Pi P
    # Pi at p -> phi(T6 T4 T0); P at end -> phi(T0 T4 T6)
    A.fwd(p, rid("m1r"))
    q = p + len(xAdj(6) + xAdj(4) + xAdj(0)) + len(P) + 3 + len(Pi)
    A.fwd(q, rid("m1"))
expandV(A, 4)
A.ins(3, (CCX01,)); A.ins(6, (CCX01,))     # CCX01 CCX01 CCX02 CCX01 CCX01 around position 3
expandV(A, 0)
pc = M(T(6), T(4), T(0), T(3), T(0), T(4), T(6))
finish("CCX12", A, pc + M(T(6), T(5), T(6)) + pc)
# X2 -> T4 T6 T0 T2
A = Asm(S, (I("X2"),)); A.fwd(0, rid("m3"))           # CX02 X0 CX02 X0
A.fwd(2, rid("m4")); A.fwd(0, rid("m4"))               # X1 CCX01 X1 CCX01 X0 X1 CCX01 X1 CCX01 X0
A.ins(8, (X0,))
finish("X2", A, M(T(4), T(6), T(0), T(2)))
# X1
A = Asm(S, (I("X1"),)); A._do((0, rid("r2"), 0, 1, False))   # CX01 X0 CX01 X0
A.fwd(2, rid("m5")); A.fwd(0, rid("m5"))               # X2 CCX02 X2 CCX02 X0 X2 CCX02 X2 CCX02 X0
A.fwd(5, rid("m6")); A.fwd(0, rid("m6"))               # phi(T4T5T4) CCX02 X0 phi(T4T5T4) CCX02 X0
n454 = len(xAdj(4) + xAdj(5) + xAdj(4))
# CCX02 -> CCX01 phi(T5) CCX01 : insert CCX01 pairs
p2 = n454 + 1 + 1 + n454
A.ins(p2, (CCX01,)); A.ins(p2 + 3, (CCX01,))
A.ins(n454, (CCX01,)); A.ins(n454 + 3, (CCX01,))
# now phi(T4T5T4T6T5T6) X0 phi(T4T5T4T6T5T6) X0 ; insert X0 X0 between blocks of the second part
blk = [xAdj(4), xAdj(5), xAdj(4), xAdj(6), xAdj(5), xAdj(6)]
pos = sum(len(b) for b in blk) + 1
for b in blk[:-1]:
    pos += len(b)
    A.ins(pos, (X0,))
    pos += 2
finish("X1", A, M(T(4), T(5), T(4), T(6), T(5), T(6), T(0), T(1), T(0), T(2), T(1), T(2)))
# CX02 -> T4 T6
A = Asm(S, (I("CX02"),)); A.fwd(0, rid("m4")); finish("CX02", A, M(T(4), T(6)))
# letter routes by one relation
def one(x, relname, pieces, fwd=True):
    A = Asm(S, (I(x),))
    if fwd: A.fwd(0, rid(relname))
    else: A.bwd(0, rid(relname))
    finish(x, A, pieces)
def base_one(x, relname, ys):
    # base relator rN (l, r) with l = [x]: relator l + rev r; rule cut at 1 replaces x by r
    A = Asm(S, (I(x),))
    A._do((0, rid(relname), 0, 1, False))
    finish(x, A, L(*ys))
A = Asm(S, (X0,)); A.fwd(0, rid("m7")); A.fwd(2, rid("m8")); A.fwd(0, rid("m8"))
finish("X0", A, L("X2", "CCX12", "X2", "CCX12", "X1", "X2", "CCX12", "X2", "CCX12", "X1"))
A = Asm(S, (I("CX01"),)); A.fwd(0, rid("m5")); finish("CX01", A, L("X2", "CCX02", "X2", "CCX02"))
A = Asm(S, (I("CX10"),)); A.fwd(0, rid("m8")); finish("CX10", A, L("X2", "CCX12", "X2", "CCX12"))
base_one("CX20", "r5", ["X1", "CCX12", "X1", "CCX12"])
base_one("CX21", "r6", ["CX20", "CX01", "CX20", "CX01"])
base_one("S01", "r13", ["CX01", "CX10", "CX01"])
base_one("S02", "r10", ["CX02", "CX20", "CX02"])
base_one("CX12", "r30", ["S01", "CX02", "S01"])
base_one("S12", "r8", ["CX12", "CX21", "CX12"])
# K12 via rK
A = Asm(S, (I("K12"),)); A._do((0, rk_rid, 0, 1, False))
k4 = kwM4567()
finish("K12", A, M(*k4) + L("X0") + M(*k4) + L("X0"))
base_one("K01", "r11", ["S02", "K12", "S02"])
base_one("CZ01", "r1", ["K12", "CX01", "K12"])
base_one("Z0", "r3", ["CZ01", "CX01", "CZ01", "CX01"])
base_one("Z1", "r4", ["K12", "X1", "K12"])
base_one("Z2", "r16", ["S02", "Z0", "S02"])
base_one("CZ02", "r18", ["S12", "CZ01", "S12"])
base_one("CZ12", "r19", ["S01", "CZ02", "S01"])
# CCZ
A = Asm(S, (I("CCZ"),))
A.ins(0, enc_w(["X2", "X1", "X0"]))
A.ins(7, enc_w(["X2", "X1", "X0"]))
finish("CCZ", A, L("X2", "X1", "X0") + M(NM) + L("X0", "X1", "X2"))
assert len(ROUTES) == 25, sorted(set(LET) - set(ROUTES))
S.save(work("store4.pkl"))
pickle.dump((ROUTES, rk_rid), open(work("routes.pkl"), "wb"))
print("routes ok", list(ROUTES))
