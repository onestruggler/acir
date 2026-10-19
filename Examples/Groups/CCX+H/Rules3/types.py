import collections, pickle
from lat import G, e8_roots, orbit, THETA
from tree import word_matrix, mat_mul
from tree2 import key
from osnf import exps
dist, reps = pickle.load(open("ball2.pkl", "rb"))
T = [word_matrix((w + " H0").strip()) for w in reps]
lvl1 = {key(Ti): i for i, Ti in enumerate(T)}
i0 = reps.index("")
kE = key(word_matrix(""))
tab = collections.Counter()
ex = {}
for j, Tj in enumerate(T):
    M = mat_mul(T[i0], Tj)
    k = key(M)
    if k == kE: continue
    c = sum(1 for Tl in T if key(mat_mul(M, Tl)) in lvl1)
    e = tuple(exps(M))
    tab[(c, e)] += 1
    ex.setdefault((c, e), reps[j])
for (c, e), n in sorted(tab.items()):
    print("common", c, "exps", e, "count", n, "example: H0", ex[(c, e)], "H0")
print("dist1 exps", tuple(exps(T[i0])))
