"""LRS-level search: words over the 106 generators, rules = Table 1 instances."""
import time
from model import table1, lev
from macro import encM
from search import RuleSet, bidir, replay
from itertools import combinations
GENS = [('n', a) for a in range(8)] + [('x', a, b) for a, b in combinations(range(8), 2)] + \
       [('k',) + q for q in combinations(range(8), 4)]
GI = {g: i for i, g in enumerate(GENS)}
T1 = table1()
RS = RuleSet()
RS.use_ins = False
for k, (fam, idx, l, r) in enumerate(T1):
    RS.add(bytes(GI[g] for g in l), bytes(GI[g] for g in r), (fam, idx))
def enc(word): return bytes(GI[g] for g in word)
def lrs_search(a, b, maxlen=None, limit=2_000_000):
    assert lev(a) == lev(b)
    res = bidir(RS, enc(a), enc(b), maxlen=maxlen or max(len(a), len(b)) + 2, limit=limit)
    return res
if __name__ == "__main__":
    N = lambda a: ('n', a); X = lambda a, b: ('x', a, b); K = lambda *q: ('k',) + q
    tests = {
      "CZ01": ([K(0,1,2,3), K(4,5,6,7), X(5,7), X(4,6), K(0,1,2,3), K(4,5,6,7)], [N(6), N(7)]),
      "Z1": ([K(0,1,2,3), K(4,5,6,7), X(5,7), X(4,6), X(1,3), X(0,2), K(0,1,2,3), K(4,5,6,7)], [N(2), N(3), N(6), N(7)]),
      "K01": ([X(3,6), X(1,4), K(0,1,2,3), K(4,5,6,7), X(3,6), X(1,4)], [K(0,2,4,6), K(1,3,5,7)]),
      "K12": ([K(4,5,6,7), X(3,7), X(2,6), X(1,5), X(0,4), K(4,5,6,7), X(3,7), X(2,6), X(1,5), X(0,4)], [K(0,1,2,3), K(4,5,6,7)]),
    }
    for nm, (a, b) in tests.items():
        t = time.time()
        r = lrs_search(a, b)
        print(nm, None if r is None else len(r), round(time.time() - t, 1), flush=True)
