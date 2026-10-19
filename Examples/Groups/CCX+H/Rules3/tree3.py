"""Distribution of path counts to distance-2 vertices; triangles."""
import sys, collections
from lat import G, e8_roots, orbit, THETA
from tree import word_matrix, mat_mul
from tree2 import key

E = frozenset(e8_roots())
H0E = frozenset(G["H0"](v) for v in E)
ot = orbit(H0E, THETA)
reps = list(ot.values())
T = [word_matrix((w + " H0").strip()) for w in reps]
I = word_matrix("")
kE = key(I)
lvl1 = {key(Ti): i for i, Ti in enumerate(T)}
# only paths through v0 = H0E (index of empty word) and compare to all: by symmetry
i0 = reps.index("")
paths = collections.Counter()
tri = 0
back = 0
for j, Tj in enumerate(T):
    k = key(mat_mul(T[i0], Tj))
    if k == kE: back += 1
    elif k in lvl1: tri += 1
    else: paths[k] += 1
print("from H0E: back", back, "triangles", tri, "new", len(paths))
# for each child of H0E, how many neighbours of E is it adjacent to?
common = collections.Counter()
for k in paths:
    pass
# compute for each child x of v0: number of neighbours a of E with x ~ a
cnt = collections.Counter()
child = {}
for j, Tj in enumerate(T):
    M = mat_mul(T[i0], Tj)
    k = key(M)
    if k == kE or k in lvl1: continue
    child[k] = M
for k, M in list(child.items())[:300]:
    c = 0
    for l, Tl in enumerate(T):
        if key(mat_mul(M, Tl)) in lvl1: c += 1
    cnt[c] += 1
print("children of H0E: # of E-neighbours adjacent (sample 300):", sorted(cnt.items()))
