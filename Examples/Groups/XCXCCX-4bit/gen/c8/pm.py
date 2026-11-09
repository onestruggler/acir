"""Perfect matchings of 8 points and the C-level orbit analysis.
Points are Gray indices 0..7 (lower states q_i, w2w1w0 = GRAY[i]).
A permutation of 8 points: tuple p with p[i] = image."""
import itertools
from m import GRAY
P8 = range(8)
ID8 = tuple(P8)
def mul(p, q):  # p then q
    return tuple(q[p[i]] for i in P8)
def inv8(p):
    r = [0]*8
    for i, x in enumerate(p): r[x] = i
    return tuple(r)
def conj(g, x):  # g^-1 x g in 'then' order = g x g^-1 as function composition:  apply g^-1, then x, then g
    return mul(mul(inv8(g), x), g)
def from_pairs(pairs):
    p = list(P8)
    for a, b in pairs: p[a], p[b] = b, a
    return tuple(p)
def pairs_of(p):
    return tuple(sorted((min(i, p[i]), max(i, p[i])) for i in P8 if i < p[i]))
PMS = sorted({from_pairs(list(zip(perm[0::2], perm[1::2]))) for perm in itertools.permutations(P8)
              if all(perm[2*k] < perm[2*k+1] for k in range(4))})
assert len(PMS) == 105
MU0 = from_pairs([(0,1),(2,3),(4,5),(6,7)])   # flip w0 in Gray indices
def union_type(mu, nu):
    # cycle lengths/2 of union graph
    seen=set(); t=[]
    for s in P8:
        if s in seen: continue
        # walk alternating
        x=s; L=0; use_mu=True
        while True:
            seen.add(x)
            x = mu[x] if use_mu else nu[x]; use_mu = not use_mu; L+=1
            if x==s and use_mu: break
        t.append(L//2)
    return tuple(sorted(t, reverse=True))
types={}
for nu in PMS:
    types.setdefault(union_type(MU0, nu), []).append(nu)
if __name__=='__main__':
    for k,v in sorted(types.items()):
        print(k, len(v))
    # Gray index <-> lower state
    print('MU0 in states:', [(format(GRAY[a],'03b'), format(GRAY[b],'03b')) for a,b in pairs_of(MU0)])
