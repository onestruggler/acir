"""The half-subgroup amalgam for charge-00 signed permutations on four
wires: even permutations of the 16 basis states with an even number of
sign changes (the diagonal and permutation part of the circuit group).
Signed permutations act on the 32 signed points +-e_x; generators are
involutions: double transpositions and sign pairs within a half."""
import sys, itertools, math
sys.path.insert(0, '..')
import core as C

n = int(sys.argv[1]) if len(sys.argv) > 1 else 4
N = 2 ** n
P = 2 * N                      # point 2x = +e_x, 2x+1 = -e_x
ID = tuple(range(P))

def mul(p, q): return tuple(q[i] for i in p)
def transp(a, b):
    p = list(range(P))
    for s in (0, 1):
        p[2 * a + s], p[2 * b + s] = 2 * b + s, 2 * a + s
    return tuple(p)
def sign(a):
    p = list(range(P)); p[2 * a], p[2 * a + 1] = 2 * a + 1, 2 * a
    return tuple(p)

def half_gens(Q):
    k = len(Q)
    s = [transp(Q[i], Q[i + 1]) for i in range(k - 1)]
    out = [mul(s[i], s[j]) for i in range(k - 1) for j in range(i + 2, k - 1)]
    out += [mul(sign(Q[i]), sign(Q[i + 1])) for i in range(k - 1)]
    return out

def closure(gens):
    W = {ID: ()}; fr = [ID]
    while fr:
        nw = []
        for p in fr:
            for k, g in enumerate(gens):
                q = mul(p, g)
                if q not in W:
                    W[q] = W[p] + (k,); nw.append(q)
        fr = nw
    return W

def relators(gens, maxlen=4):
    rels = set(); m = len(gens)
    for L in range(2, maxlen + 1):
        for w in itertools.product(range(m), repeat=L):
            p = ID
            for k in w: p = mul(p, gens[k])
            if p == ID:
                rels.add(min(w[i:] + w[:i] for i in range(L)))
    for a, b in itertools.combinations(range(m), 2):
        p = mul(gens[a], gens[b]); q = p; k = 1
        while q != ID:
            q = mul(q, p); k += 1
        rels.add((a, b) * k)
    return sorted(rels)

halves = [(w, b) for w in range(n) for b in (0, 1)]
hp = {h: [x for x in range(N) if (x >> h[0] & 1) == h[1]] for h in halves}
offset, allgens = {}, []
for h in halves:
    offset[h] = len(allgens); allgens += half_gens(hp[h])
m = len(half_gens(hp[halves[0]]))
loc = relators(half_gens(list(range(N // 2))), maxlen=3)
horder = 2 ** (N // 2 - 1) * math.factorial(N // 2) // 2
print('gens per half', m, 'local relators', len(loc), flush=True)
signs = [(k,) for k, g in enumerate(half_gens(list(range(N // 2)))) if k >= len(half_gens(list(range(N // 2)))) - (N // 2 - 1)]
print('local presentation: index over the sign pairs', C.index_c(m, loc, signs, limit=10_000_000), 'expected', horder // 2 ** (N // 2 - 1), flush=True)
rels = []
for h in halves:
    rels += [tuple(offset[h] + k for k in w) for w in loc]
tables = {h: closure(half_gens(hp[h])) for h in halves}
print('half tables', len(tables[halves[0]]), flush=True)
for h, h2 in itertools.combinations(halves, 2):
    if h[0] == h2[0]:
        continue
    Q = [x for x in hp[h] if x in hp[h2]]
    for g in half_gens(Q):
        w1 = tuple(offset[h] + k for k in tables[h][g])
        w2 = tuple(offset[h2] + k for k in tables[h2][g])
        rels.append(w1 + tuple(reversed(w2)))
for w in range(n):
    for a in range(m):
        for b in range(m):
            ga, gb = offset[(w, 0)] + a, offset[(w, 1)] + b
            rels.append((ga, gb, ga, gb))
sub = [(offset[(n - 1, 0)] + k,) for k in range(m)] + [(offset[(n - 1, 1)] + k,) for k in range(m)]
G = 2 ** (N - 1) * math.factorial(N) // 2
expect = G // horder ** 2
print('relators', len(rels), 'expected index', expect, flush=True)
print('index', C.index_c(len(allgens), rels, sub, limit=20_000_000), flush=True)
