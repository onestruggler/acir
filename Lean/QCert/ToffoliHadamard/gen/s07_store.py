from paths import work, data, module
import pickle
from store import Store
from model import LET, IDX, xAdj, eq
rels3, names3, found = pickle.load(open(work("phase3.pkl"),"rb"))
relsc, namesc, found_c, res = pickle.load(open(work("t3c.pkl"),"rb"))
rels2, names2, derived = pickle.load(open(work("sat2_4_5_6.pkl"),"rb"))
assert relsc[:len(rels3)] == rels3 and rels3[:len(rels2)] == rels2
der = [None] * 71
d2 = {rid: (u, v, st) for (c, u, v, st, rid) in derived}
for rid in range(71, len(rels2)):
    der.append(d2[rid])
for rid in range(len(rels2), len(rels3)):
    nm = names3[rid]
    st = found[nm]
    rho = rels3[rid]
    # find split: u = a, v = b with rho = a + rev b, replay(a, st) == b
    from cbfs import Relators
    der.append(("SPLIT", nm, st))
for rid in range(len(rels3), len(relsc)):
    der.append(("SPLIT", namesc[rid], None))
# resolve splits: try all cut points
S = Store(relsc, namesc, [None]*len(relsc))
resmap = {str(k) if not (isinstance(k, tuple) and k[0]=="conjP") else f"conjP{k[1]}": v for k, v in res.items()}
for rid in range(len(rels3), len(relsc)):
    der[rid] = ("SPLIT", namesc[rid], resmap[namesc[rid]])
for rid, d in enumerate(der):
    if d is not None and d[0] == "SPLIT":
        _, nm, st = d
        rho = S.R.rels[rid]
        ok = None
        for cut in range(len(rho) + 1):
            u = rho[:cut]; v = tuple(reversed(rho[cut:]))
            try:
                if S.R.replay(u, st) == v:
                    ok = (u, v, st); break
            except AssertionError:
                pass
        assert ok, nm
        der[rid] = ok
S.der = der
# verify every derivation
for rid, d in enumerate(der):
    if d is None: continue
    u, v, st = d
    assert S.R.replay(u, st) == v, rid
    assert tuple(u) + tuple(reversed(v)) == S.R.rels[rid]
    assert all(s[1] < rid for s in st), ("forward ref", rid)
S.save(work("store1.pkl"))
print("ok", len(der))
