from paths import work, data, module
import sys, time
from store import Store
from asm import Asm
from gsearch import gq
from model import LET, IDX, xAdj, eq
from sat2 import enc_w
S = Store.load(work("store1.pkl"))
C = S.search(10)
def W(s): return enc_w(s.split()) if isinstance(s, str) else enc_w(s)
P = W("X0 X2 CCX01 X0"); Pi = W("X0 CCX01 X2 X0"); V = W("CCX12 CCX02 CCX12")
T = {i: enc_w(xAdj(i)) for i in range(7)}
Y5a = W("CCX01 X2 CCX02 X2 CCX01"); Y5 = W("CCX02 X1 CCX01 X1 CCX02")
def search_add(a, b, name, limit=3000000, extras=(2,4,6)):
    st = gq(C, a, b, limit, add=True, name=name, extras=extras, verbose=False)
    assert st is not None, name
    assert S.R.names[-1] == name
    S.der.append((tuple(a), tuple(b), st))
    return S.find(name)
r_c5a = search_add(Pi + T[5] + P, Y5a, "conjP5a")
r_br = search_add(Y5a, Y5, "Y5bridge")
print("searched", flush=True)
cp = {k: S.find(f"conjP{k}") for k in (0, 1, 2, 4, 6)}
fv = {k: S.find(str(("farV", k))) for k in (0, 1, 5, 6)}
bv = {k: S.find(str(("braidV", k))) for k in (2, 4)}
assert S.der[fv[5]][0] == V + Y5
newrels = {}
# far(3,k)
for k in (0, 1, 5, 6):
    a = T[3] + T[k]; b = T[k] + T[3]
    A = Asm(S, a)
    n = len(P) + len(V) + len(Pi) + len(T[k])
    A.ins(n, P)                      # P V Pi T_k P Pi
    off = len(P) + len(V)
    if k == 5:
        A.fwd(off, r_c5a); A.fwd(off, r_br)
    else:
        A.fwd(off, cp[k])            # P V Y Pi
    A.fwd(len(P), fv[k])             # P Y V Pi
    if k == 5:
        A.bwd(len(P), r_br); A.bwd(len(P), r_c5a)
    else:
        A.bwd(len(P), cp[k])         # P Pi T_k P V Pi
    A.cancel(0, P)
    assert A.w == b, k
    lo, hi = min(3, k), max(3, k)
    name = f"far{lo}{hi}"
    # orient as T_lo T_hi -> T_hi T_lo
    if k < 3:
        S.add(b, a, [S.R.inverse(st) for st in reversed(A.steps)], name)
    else:
        S.add(a, b, A.steps, name)
# braid2: T2 T3 T2 -> T3 T2 T3
a = T[2] + T[3] + T[2]; b = T[3] + T[2] + T[3]
A = Asm(S, a)
A.ins(0, P)                                  # P Pi T2 P V Pi T2
A.fwd(len(P), cp[2])                         # P T2 V Pi T2
A.ins(len(A.w), P)                           # P T2 V Pi T2 P Pi
A.fwd(len(P) + len(T[2]) + len(V), cp[2])    # P T2 V T2 Pi
A.fwd(len(P), bv[2])                         # P V T2 V Pi
A.bwd(len(P) + len(V), cp[2])                # P V Pi T2 P V Pi
assert A.w == b
S.add(a, b, A.steps, "braid2")
# braid3: T3 T4 T3 -> T4 T3 T4
a = T[3] + T[4] + T[3]; b = T[4] + T[3] + T[4]
A = Asm(S, a)
A.fwd(len(P) + len(V), cp[4])                # P V T4 V Pi
A.fwd(len(P), bv[4])                         # P T4 V T4 Pi
A.bwd(len(P) + len(T[4]) + len(V), cp[4])    # P T4 V Pi T4 P Pi
A.bwd(len(P), cp[4])                         # P Pi T4 P V Pi T4 P Pi
A.cancel(0, P)
A.cancel(len(A.w) - 2 * len(P), P)
assert A.w == b
S.add(a, b, A.steps, "braid3")
# braid0 from braid4
b4 = S.find("braid4")
a = T[0] + T[1] + T[0]; b = T[1] + T[0] + T[1]
X0 = IDX["X0"]
A = Asm(S, a)
# T0 = X0 T4 X0, T1 = X0 T5 X0 literally
A.cancel(len(T[0]) - 1, (X0,))
A.cancel(len(T[0]) - 1 + len(T[5]), (X0,))
A.fwd(1, b4)
A.ins(1 + len(T[5]), (X0,))
A.ins(1 + len(T[5]) + 2 + len(T[4]), (X0,))
assert A.w == b
S.add(a, b, A.steps, "braid0")
S.save(work("store2.pkl"))
# list all Coxeter relators
for i in range(7):
    for j in range(i + 2, 7):
        rid = S.find(f"far{i}{j}")
        u, v, st = S.der[rid]
        assert (u, v) == (T[i] + T[j], T[j] + T[i]), (i, j)
for i in range(6):
    rid = S.find(f"braid{i}")
    u, v, st = S.der[rid]
    assert (u, v) == (T[i] + T[i+1] + T[i], T[i+1] + T[i] + T[i+1]), i
print("all 21 Coxeter relations derived")
C.close()
