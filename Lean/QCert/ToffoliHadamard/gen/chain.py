from paths import work, data, module
import pickle, time, sys
from model import LET, IDX, eq, xAdj
from cbfs import Relators, CSearch
from sat2 import enc_w

def load(fn=None, maxlhs=6):
    fn = fn or work("phase3.pkl")
    rels, names, found = pickle.load(open(fn, "rb"))
    R = Relators()
    for r, n in zip(rels, names):
        R.add(r, n)
    return R, CSearch(len(LET), maxlhs, R), found

def chain_search(S, words, limit=500000, extra=2, add=False, name="c"):
    steps = []
    for k in range(len(words) - 1):
        a = enc_w(words[k]); b = enc_w(words[k+1])
        assert eq(words[k], words[k+1]), (k, words[k], words[k+1])
        ml = min(25, max(len(a), len(b)) + extra)
        t = time.time()
        res = S.query(a, b, ml, limit)
        print("  link", k, len(a), len(b), "->", None if res is None else len(res), round(time.time()-t,1), flush=True)
        if res is None:
            return None
        steps += res
    if add:
        S.rels.add(enc_w(words[0]) + tuple(reversed(enc_w(words[-1]))), name)
    return steps
