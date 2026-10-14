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


# ---------------------------------------------------------------------
# With derived letters: reversed CNOTs and swaps

DERIVED = {"CXr0": "HH0 CX0 HH0", "CXr1": "HH1 CX1 HH1",
           "SW0": "CX0 HH0 CX0 HH0 CX0", "SW1": "CX1 HH1 CX1 HH1 CX1"}

def derived_setup():
    a = S.Alphabet(gs, DERIVED)
    return a

def test_alpha(a, rels, subgroup_names, limit=20_000_000):
    assert S.sound(rep, a, rels)
    t = time.time()
    got = C.index_c(len(a.letters), list(rels) + a.definitions(),
                    [(a.index[n],) for n in subgroup_names], limit)
    return got, time.time() - t

def run_derived(maxlen, limit=20_000_000):
    a = derived_setup()
    base = a.structural() + [r for t in TWO for r in S.rule(a, t)]
    span = lambda r: {w for g in r for w in a.wires[g]} == {0, 1, 2}
    cands = [r for r in S.relators(rep, a, range(len(a.letters)), (maxlen + 1) // 2)
             if len(r) <= maxlen and span(r)]
    print(f"derived alphabet ({len(a.letters)} letters): genuine relators up to length {maxlen}: {len(cands)}", flush=True)
    got, dt = test_alpha(a, base + cands, ["X0","X1","X2","CX0","CX1","CCX0"], limit)
    print(f"  index over K: {got} (expect 5443200)  {dt:.0f}s", flush=True)
    return a, base, cands


# ---------------------------------------------------------------------
# Certification and minimisation through the subgroup S8

CLASSICAL = ["X0","X1","X2","CX0","CX1","CCX0","CXr0","CXr1","SW0","SW1"]
ADJ = ["X0","X1","X2","CX0","CX1","CCX0"]

def checks(a, rels, use_c=True):
    """(index of <X> in P_S8, index of S8 in G_R): complete iff (5040, 17280)."""
    S8 = [a.index[n] for n in CLASSICAL]
    Xs = [a.index[n] for n in ["X0","X1","X2"]]
    p = S.restricted_index(a, rels, S8, Xs, limit=2_000_000)
    if p != 5040:
        return p, None
    g = C.index_c(len(a.letters), list(rels) + a.definitions(), [(x,) for x in S8], 2_000_000)
    return p, g

def certify_adjacent(a, rels):
    """|P_K| for K the adjacent classical gates (expect 128)."""
    K = [a.index[n] for n in ADJ]
    return S.restricted_index(a, rels, K, (), limit=2_000_000)
