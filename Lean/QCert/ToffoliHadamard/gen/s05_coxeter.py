from paths import work, data, module
import pickle, time, sys
from model import LET, IDX, eq, xAdj
from cbfs import Relators, CSearch
from sat2 import enc_w

rels, names, derived = pickle.load(open(work("sat2_4_5_6.pkl"), "rb"))
R = Relators()
for r, n in zip(rels, names):
    R.add(r, n)
maxlhs = int(sys.argv[1]) if len(sys.argv) > 1 else 6
limit = int(sys.argv[2]) if len(sys.argv) > 2 else 2_000_000
extra = int(sys.argv[3]) if len(sys.argv) > 3 else 2
S = CSearch(len(LET), maxlhs, R)

def T(i):
    return xAdj(i)

tests = []
for i in range(7):
    for j in range(i + 2, 7):
        tests.append((f"far{i}{j}", T(i) + T(j), T(j) + T(i)))
for i in range(6):
    tests.append((f"braid{i}", T(i) + T(i + 1) + T(i), T(i + 1) + T(i) + T(i + 1)))
tests.sort(key=lambda t: len(t[1]) + len(t[2]))
found = {}
for name, l, r in tests:
    a = enc_w(l); b = enc_w(r)
    ml = min(25, max(len(a), len(b)) + extra)
    t = time.time()
    res = S.query(a, b, ml, limit, add=True, name=name)
    print(name, len(a), len(b), "->", None if res is None else len(res), round(time.time() - t, 1), "s", flush=True)
    if res is not None:
        found[name] = res
pickle.dump((R.rels, R.names, found), open(work("phase3.pkl"), "wb"))
S.close()
