from paths import work, data, module
from chain import *
from gsearch import gq
from model import ev
import sys
R, S, found = load(maxlhs=int(sys.argv[2]))
P = "X0 X2 CCX01 X0".split(); Pi = "X0 CCX01 X2 X0".split()
V = "CCX12 CCX02 CCX12".split()
assert P + V + Pi == xAdj(3)
Y = {0: xAdj(0), 2: xAdj(2), 4: xAdj(4), 6: xAdj(6),
     1: "X0 X2 CCX02 X2 X0".split(),
     5: "CCX02 X1 CCX01 X1 CCX02".split()}
res = {}
for k in (0,1,2,4,5,6):
    l = Pi + xAdj(k) + P
    assert eq(l, Y[k]), k
    a, b = enc_w(l), enc_w(Y[k])
    t = time.time()
    st = gq(S, a, b, int(sys.argv[1]), add=True, name=f"conjP{k}")
    print("conjP", k, len(a), len(b), "->", None if st is None else len(st), round(time.time()-t,1), flush=True)
    res[("conjP", k)] = st
rel = {}
for k in (0,1,5,6):
    rel[("farV", k)] = (V + Y[k], Y[k] + V)
rel[("braidV", 2)] = (Y[2] + V + Y[2], V + Y[2] + V)
rel[("braidV", 4)] = (V + Y[4] + V, Y[4] + V + Y[4])
for key, (l, r) in rel.items():
    assert eq(l, r), key
    a, b = enc_w(l), enc_w(r)
    t = time.time()
    st = gq(S, a, b, int(sys.argv[1]), add=True, name=str(key))
    print(key, len(a), len(b), "->", None if st is None else len(st), round(time.time()-t,1), flush=True)
    res[key] = st
pickle.dump((R.rels, R.names, found, res), open(work("t3c.pkl"), "wb"))
S.close()
