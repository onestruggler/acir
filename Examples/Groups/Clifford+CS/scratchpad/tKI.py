# The hybrid letter ki a b s = K_[a,b] i_[s]^-1 in place of the K pair.
# Checks, on exact matrices: (1) every ki rule of the redesigned P'
# (each the image of a two-level K relation under the frame embedding
# Phi(i_a) = pw a s, Phi(X_ab) = xw s a b, Phi(K_ab) = ki a b s, plus
# the sink move) at every admissible index assignment; (2) the coset
# action with the uniform K row i_0^c i_t^-c . ki d e t . (i_t i_0^-1)^(c+1),
# t the first numeral off 0, d, e, at every generator and coset; (3) the
# frame transport act c y = T c . Phi y . T^- c', T c = (i_0 i_g^-1)^c,
# for every generator, coset and sink g off 0 and the generator.
import sys
from itertools import combinations, permutations, product
import csP

N = int(sys.argv[1]) if len(sys.argv) > 1 else 8
mm = csP.matmul

def ig(a): return csP.two_level(N, 'i', a)
def Xg(a, b): return csP.two_level(N, 'X', a, b)
def Kg(a, b): return csP.two_level(N, 'K', a, b)
def prod(ms):
    M = csP.ident(N)
    for m in ms: M = mm(M, m)
    return M
def inv_i(a): return prod([ig(a)] * 3)

def pw(a, b): return mm(ig(a), inv_i(b))
def xw(c, a, b): return prod([ig(c), ig(c), Xg(a, b)])
def dw(a, b, c, d): return mm(Xg(a, b), Xg(c, d))
def ki(a, b, s): return mm(Kg(a, b), inv_i(s))
def eq(A, B): return csP.key(A) == csP.key(B)
I = csP.ident(N)

bad = {}
def note(name, ok):
    bad.setdefault(name, [0, 0])
    bad[name][1] += 1
    if not ok: bad[name][0] += 1

idx = range(N)
prs = list(combinations(idx, 2))
for (a, b) in prs:
    for s in idx:
        for t in idx:
            note('ki-sink', eq(mm(ki(a, b, s), pw(s, t)), ki(a, b, t)))
        if s in (a, b): continue
        K = ki(a, b, s)
        for x in idx:
            if x in (a, b): continue
            note('ki-pp', eq(mm(pw(x, s), K), mm(K, pw(x, s))))
        for (x, y) in prs:
            if {x, y} & {a, b} or s in (x, y): continue
            note('ki-px', eq(mm(xw(s, x, y), K), mm(K, xw(s, x, y))))
        for (c, d) in prs:
            if {c, d} & {a, b} or s in (c, d): continue
            note('ki-ki', eq(mm(K, ki(c, d, s)), mm(ki(c, d, s), K)))
        note('ki-x', eq(prod([K, pw(b, s), pw(b, s)]), mm(xw(s, a, b), K)))
        note('ki-16', eq(prod([K, pw(b, s), pw(b, s), pw(b, s)]),
                         prod([pw(b, s), K, pw(b, s), K])))
        note('ki-ii', eq(prod([K, pw(a, s), pw(b, s)]), prod([pw(a, s), pw(b, s), K])))
        note('ki-sq', eq(prod([K, K, pw(a, s), pw(b, s)]), I))
for j, k, l in combinations(idx, 3):
    for s in idx:
        if s in (j, k, l): continue
        note('ki-swap', eq(mm(ki(k, l, s), xw(s, j, k)), mm(xw(s, j, k), ki(j, l, s))))
        note('ki-swap2', eq(mm(ki(j, l, s), xw(s, k, l)), mm(xw(s, k, l), ki(j, k, s))))
for j, k, l, m in permutations(idx, 4):
    if not (j < k and l < m and j < l and k < m): continue
    for s in idx:
        if s in (j, k, l, m): continue
        note('ki-yb', eq(prod([ki(j, k, s), ki(l, m, s), ki(j, l, s), ki(k, m, s)]),
                         prod([ki(j, l, s), ki(k, m, s), ki(j, k, s), ki(l, m, s)])))
print('rules (failing/instances):', {k: tuple(v) for k, v in bad.items()})

# The action.
def fresh(avoid):
    x = 0
    while x in avoid: x += 1
    return x

def pows(c, M): return prod([M] * c)

def act(c, g):
    kind = g[0]
    if kind == 'i':
        return pw(g[1], 0), (c + 1) % 4
    if kind == 'X':
        _, b, cc = g
        if b != 0:
            return xw(0, b, cc), (c + 2) % 4
        return mm(xw(cc, 0, cc), pows(c, pw(cc, 0))), (c + 2) % 4
    _, d, e = g
    t = fresh({0, d, e})
    return prod([pows(c, pw(0, t)), ki(d, e, t), pows(c + 1, pw(t, 0))]), (c + 1) % 4

def gens():
    for a in idx: yield ('i', a)
    for a, b in prs: yield ('X', a, b)
    for a, b in prs: yield ('K', a, b)

def gmat(g):
    if g[0] == 'i': return ig(g[1])
    return csP.two_level(N, g[0], g[1], g[2])

def deg(g): return 2 if g[0] == 'X' else 1

reps = [pows(c, ig(0)) for c in range(4)]
repsi = [pows(c, inv_i(0)) for c in range(4)]
tot = badA = 0
for g in gens():
    for c in range(4):
        W, c2 = act(c, g)
        tot += 1
        if not eq(prod([reps[c], gmat(g), repsi[c2]]), W): badA += 1
print(f'action: {tot - badA}/{tot} cases check')

def Phi(g, s):
    if g[0] == 'i': return pw(g[1], s)
    if g[0] == 'X': return xw(s, g[1], g[2])
    return ki(g[1], g[2], s)

tot = badT = 0
for g in gens():
    for s in idx:
        if s == 0 or s in g[1:]: continue
        for c in range(4):
            W, c2 = act(c, g)
            tot += 1
            T = pows(c, pw(0, s)); Tm = pows(c2, pw(s, 0))
            if not eq(W, prod([T, Phi(g, s), Tm])): badT += 1
print(f'frame transport: {tot - badT}/{tot} cases check')
