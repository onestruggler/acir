from paths import work, data, module
import pickle, time, sys
from model import LET, IDX, eq
from rels import FIG4, FIG7, RK
from cbfs import Relators, CSearch

def enc_w(ws):
    return tuple(IDX[x] for x in ws)

def relator(l, r):
    return tuple(l) + tuple(reversed(r))

def canon(rho):
    n = len(rho); best = None
    for base in (rho, tuple(reversed(rho))):
        for r in range(n):
            c = base[r:] + base[:r]
            if best is None or c < best:
                best = c
    return best

def base_relators():
    R = Relators()
    for x in LET:
        R.add(enc_w([x, x]), f"inv_{x}")
    for n, l, r in FIG4:
        R.add(enc_w(relator(l, r)), f"r{n}")
    return R

if __name__ == "__main__":
    rels6 = pickle.load(open(work("relators6.pkl"), "rb"))
    R = base_relators()
    known = set(canon(r) for r in R.rels)
    S = CSearch(len(LET), int(sys.argv[3]) if len(sys.argv) > 3 else 8, R, first=True)
    maxlen = int(sys.argv[1]); limit = int(sys.argv[2])
    Ls = [int(x) for x in (sys.argv[4] if len(sys.argv) > 4 else "4,5").split(",")]
    derived = []
    t0 = time.time()
    for rnd in range(30):
        prog = 0
        for L in Ls:
            for c in sorted(rels6[L]):
                if c in known:
                    continue
                h = len(c) // 2
                u = c[:h]; v = tuple(reversed(c[h:]))
                res = S.query(u, v, maxlen, limit, add=True, name=f"d{len(derived)}")
                if res is None:
                    continue
                known.add(c)
                derived.append((c, u, v, res, len(R.rels) - 1))
                prog += 1
        left = sum(1 for L in Ls for c in rels6[L] if c not in known)
        print("round", rnd, "derived", prog, "left", left, round(time.time() - t0), "s", flush=True)
        if prog == 0:
            break
    pickle.dump((R.rels, R.names, derived), open(work(f"sat2_{'_'.join(map(str,Ls))}.pkl"), "wb"))
    for L in Ls:
        bad = [c for c in sorted(rels6[L]) if c not in known]
        for c in bad[:30]:
            print(L, " ".join(LET[x] for x in c))
    S.close()
