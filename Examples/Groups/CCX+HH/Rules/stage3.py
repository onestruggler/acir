"""Width-3 completeness experiments (run under WSL python with ./tc built)."""
import sys, time
from collections import Counter
sys.path.insert(0, '.')
import core as C, staged as S

gs = C.GateSet(3); rep = C.PermRep(gs)
alpha = S.Alphabet(gs)
L = alpha.index
K = [L[n] for n in ["X0","X1","X2","CX0","CX1","CCX0"]]
ORDER = 696729600

def order_of(letters):
    seen = {rep.identity}; frontier = [rep.identity]
    while frontier:
        new = []
        for p in frontier:
            for g in letters:
                q = tuple(rep.gens[g][x] for x in p)
                if q not in seen: seen.add(q); new.append(q)
        frontier = new
    return len(seen)

if __name__ == "__main__":
    k = order_of(K); print("classical adjacent subgroup order:", k, "expected index", ORDER // k)
    for half in (4, 5):
        t = time.time(); cands = S.relators(rep, alpha, range(len(alpha.letters)), half)
        print(f"half {half}: {len(cands)} relators", dict(sorted(Counter(map(len, cands)).items())), f"{time.time()-t:.0f}s")

TWO = ["X1 CX0 X1 = CX0 X0",
       "X0 HH0 X1 HH0 X0 HH0 X1 HH0",
       "X0 X1 HH0 CX0 HH0 X0 HH0 CX0 HH0",
       "CX0 HH0 CX0 HH0 CX0 HH0 CX0 HH0 CX0 HH0 CX0 HH0"]

def base_rules():
    return alpha.structural() + [r for t in TWO for r in S.rule(alpha, t)]

def spans3(r):
    ws = {w for g in r for w in alpha.wires[g]}
    return ws == {0, 1, 2}

def test(extra, limit=20_000_000):
    rels = base_rules() + list(extra)
    assert S.sound(rep, alpha, rels)
    t = time.time()
    got = C.index_c(len(alpha.letters), rels, [(g,) for g in K], limit)
    return got, time.time() - t

def run_genuine(maxlen):
    cands = [r for r in S.relators(rep, alpha, range(len(alpha.letters)), (maxlen + 1) // 2)
             if len(r) <= maxlen and spans3(r)]
    print(f"genuine 3-wire relators up to length {maxlen}: {len(cands)}", flush=True)
    got, dt = test(cands)
    print(f"  index over K: {got} (expect 5443200)  {dt:.0f}s", flush=True)
    return cands
