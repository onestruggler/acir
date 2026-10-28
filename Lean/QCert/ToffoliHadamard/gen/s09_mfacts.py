from paths import work, data, module
import sys, time
from store import Store
from gsearch import gq
from model import LET, IDX, xAdj, eq
from sat2 import enc_w
S = Store.load(work("store2.pkl"))
C = S.search(10)
def W(s): return enc_w(s.split())
facts = {
  "m1": ("X0 X2 CCX01 X0", " ".join(xAdj(0) + xAdj(4) + xAdj(6))),
  "m1r": ("X0 CCX01 X2 X0", " ".join(xAdj(6) + xAdj(4) + xAdj(0))),
  "m2": ("CCX12", "CCX12 CCX02 CCX12 CCX02 CCX12 CCX02 CCX12"),
  "m3": ("X2", "CX02 X0 CX02 X0"),
  "m4": ("CX02", "X1 CCX01 X1 CCX01"),
  "m5": ("CX01", "X2 CCX02 X2 CCX02"),
  "m6": ("X2 CCX02 X2", " ".join(xAdj(4) + xAdj(5) + xAdj(4))),
  "m7": ("X0", "CX10 X1 CX10 X1"),
  "m8": ("CX10", "X2 CCX12 X2 CCX12"),
}
for nm, (a, b) in facts.items():
    a = W(a); b = W(b)
    assert eq([LET[x] for x in a], [LET[x] for x in b]), nm
    t = time.time()
    st = gq(C, a, b, int(sys.argv[1]) if len(sys.argv) > 1 else 2000000, add=True, name=nm, extras=(2, 4, 6), verbose=False)
    print(nm, len(a), len(b), None if st is None else len(st), round(time.time() - t, 1), flush=True)
    if st is not None:
        assert S.R.names[-1] == nm
        S.der.append((tuple(a), tuple(b), st))
    else:
        break
S.save(work("store3.pkl"))
C.close()
