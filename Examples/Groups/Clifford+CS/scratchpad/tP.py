# The coset-action table for the Clifford+CS >= 4-wire design
# (four-wire-notes.md, item (a)): act(c, g) = (word over P', c + deg g)
# with r_c . g = (word) . r_{c+deg g}, r_c = i_0^c, checked exactly on
# N x N matrices for every generator and coset.  The tA2.py analogue.
import sys
import csP
from itertools import combinations

N = int(sys.argv[1]) if len(sys.argv) > 1 else 16

LET = {}
def letter(name):
    if name in LET: return LET[name]
    kind = name[0]
    if kind == 'iib':
        _, a, b = name
        M = csP.matmul(csP.two_level(N, 'i', a), csP.minv('i', N, b))
    elif kind == 'mX':
        _, a, b, c = name
        m = csP.matmul(csP.two_level(N, 'i', a), csP.two_level(N, 'i', a))
        M = csP.matmul(m, csP.two_level(N, 'X', b, c))
    elif kind == 'XX':
        _, a, b, c, d = name
        M = csP.matmul(csP.two_level(N, 'X', a, b), csP.two_level(N, 'X', c, d))
    elif kind == 'KKb':
        _, a, b, c, d = name
        M = csP.matmul(csP.two_level(N, 'K', a, b), csP.minv('K', N, c, d))
    LET[name] = M
    return M

def wordmat(w):
    M = csP.ident(N)
    for name in w:
        M = csP.matmul(M, letter(name))
    return M

def fresh(avoid, k):
    out = []
    x = 0
    while len(out) < k:
        if x not in avoid and x not in out: out.append(x)
        x += 1
    return out

def Q(z, w, u, v):
    # K_0z i_0^-1  (the c = 0 pattern, 1 -> z, 2 -> w, (3,4) -> (u,v))
    return [('iib', z, 0), ('iib', w, 0), ('KKb', 0, z, u, v),
            ('iib', 0, w), ('KKb', u, v, 0, z)]

def K0_word(c, e, w, u, v):
    # i_0^c K_0e i_0^-(c+1), the four tabulated patterns (1 -> e;
    # 2 -> w, (3,4) -> (u,v) for c even; (2,3) -> (u,v), 4 -> w for odd)
    B_ev = ('KKb', 0, e, u, v); Bi_ev = ('KKb', u, v, 0, e)
    if c == 0:
        return [('iib', e, 0), ('iib', w, 0), B_ev, ('iib', 0, w), Bi_ev]
    if c == 2:
        return [('iib', e, 0), ('iib', w, 0), B_ev, ('iib', e, w), Bi_ev]
    if c == 1:
        return [('iib', e, 0), B_ev, ('iib', 0, w), Bi_ev, ('iib', w, 0)]
    return [('iib', e, 0), B_ev, ('iib', w, 0), Bi_ev, ('iib', e, w)]

def act_word(c, g):
    kind = g[0]
    if kind == 'i':
        _, a = g
        return [] if a == 0 else [('iib', a, 0)]
    if kind == 'X':
        _, b, cc = g
        if 0 not in (b, cc):
            return [('mX', 0, b, cc)]
        e = cc if b == 0 else b
        return [('mX', e, 0, e)] + [('iib', e, 0)] * c
    _, d, e = g
    if 0 not in (d, e):
        z, w, u, v = fresh({0, d, e}, 4)
        return [('KKb', d, e, 0, z)] + Q(z, w, u, v)
    ee = e if d == 0 else d
    w, u, v = fresh({0, ee}, 3)
    return K0_word(c, ee, w, u, v)

def deg(g):
    return 2 if g[0] == 'X' else 1

def gmat(g):
    if g[0] == 'i': return csP.two_level(N, 'i', g[1])
    return csP.two_level(N, g[0], g[1], g[2])

i0 = csP.two_level(N, 'i', 0)
i0i = csP.minv('i', N, 0)
reps = [csP.ident(N)]
repsi = [csP.ident(N)]
for _ in range(4):
    reps.append(csP.matmul(reps[-1], i0))
    repsi.append(csP.matmul(repsi[-1], i0i))

gens = [('i', a) for a in range(N)]
gens += [('X', a, b) for a, b in combinations(range(N), 2)]
gens += [('K', a, b) for a, b in combinations(range(N), 2)]

bad = 0; tot = 0
for g in gens:
    Mg = gmat(g)
    for c in range(4):
        c2 = (c + deg(g)) % 4
        # r_c . g . r_c2^-1 == word
        T = csP.matmul(reps[c], csP.matmul(Mg, repsi[c2]))
        W = wordmat(act_word(c, g))
        tot += 1
        if csP.key(T) != csP.key(W):
            bad += 1
            if bad <= 6: print('FAIL', c, g, act_word(c, g), flush=True)
print(f'N={N}: {tot - bad}/{tot} action-table cases check', flush=True)
