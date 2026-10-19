"""Common neighbours of (E, x) for x of types 6 and 2; their mutual relative positions."""
import collections
from geo import d, rel_dist, neighbours, T, I8, REPS
from tree import word_matrix, mat_mul
from osnf import exps

def commons(g, h):
    return [y for _, y in neighbours(g) if rel_dist(y, h) == 1]

for name, w in [("type30", "H0 CCX0 H0"), ("type6", "H0 CCX0 CX10 CCX0 H0"),
                ("type2", "H0 CCX0 CX20 CCX0 CX10 CCX0 H0")]:
    x = word_matrix(w)
    cs = commons(I8, x)
    print(name, "commons", len(cs))
    pat = collections.Counter()
    adj = {i: [] for i in range(len(cs))}
    for i in range(len(cs)):
        for j in range(i + 1, len(cs)):
            # relative exponent pattern of cs[i], cs[j]
            gT = cs[i]
            e = tuple(exps(mat_mul([[c for c in col] for col in __import__('geo').transpose(cs[i])], cs[j])))
            pat[e] += 1
            if e == (-2, 0, 0, 0, 0, 0, 0, 2):
                adj[i].append(j); adj[j].append(i)
    # connectivity
    seen = {0}; fr = [0]
    while fr:
        n = []
        for u in fr:
            for v in adj[u]:
                if v not in seen: seen.add(v); n.append(v)
        fr = n
    print("  pair patterns", dict(pat), "j=1-connected:", len(seen) == len(cs))
