# Which diagonal bridge / pair-scalar facts of the hybrid split into
# factors the hybrid provably passes (phase functions mod 4)?
import itertools, sys
from dec import code, layout
n = 4; N = 16
ST = list(itertools.product((0, 1), repeat=4))           # states as bit tuples, wire i = index i
IDX = {s: i for i, s in enumerate(ST)}
def roles(a):
    t, x = layout(n, a)
    canon = {0: t}
    rest = [w for w in range(4) if w != t]               # canonical 1.. -> actual in order
    for k, w in enumerate(rest): canon[k + 1] = w
    single = canon[3]; pair = [canon[1], canon[2]]
    return t, x, pair, single

def hnf_member(gens, v, mod=4):
    """is v in the Z-span of gens + mod * e_i (mod 4 module)?"""
    rows = [list(g) for g in gens] + [[mod if j == i else 0 for j in range(N)] for i in range(N)]
    piv = []
    r = 0
    for col in range(N):
        # gcd-reduce column col among rows r..
        while True:
            nz = [i for i in range(r, len(rows)) if rows[i][col] != 0]
            if not nz: break
            m = min(nz, key=lambda i: abs(rows[i][col]))
            rows[r], rows[m] = rows[m], rows[r]
            done = True
            for i in range(r + 1, len(rows)):
                if rows[i][col]:
                    q = rows[i][col] // rows[r][col]
                    rows[i] = [a - q * b for a, b in zip(rows[i], rows[r])]
                    if rows[i][col]: done = False
            if done: break
        if any(rows[i][col] for i in range(r, len(rows))) or (r < len(rows) and rows[r][col]):
            if rows[r][col]:
                piv.append((r, col)); r += 1
    v = list(v)
    for (ri, col) in piv:
        if v[col] % rows[ri][col]: return False
        q = v[col] // rows[ri][col]
        v = [a - q * b for a, b in zip(v, rows[ri])]
    return all(a == 0 for a in v)

def menu(a, use_single_target=True):
    t, x, pair, single = roles(a)
    ctrl = [w for w in range(4) if w != t]
    gens = []
    # (a) functions of the controls only
    for w in ctrl: gens.append([s[w] for s in ST])
    for v, w in itertools.combinations(ctrl, 2): gens.append([s[v] * s[w] for s in ST])
    gens.append([2 * s[ctrl[0]] * s[ctrl[1]] * s[ctrl[2]] for s in ST])
    # (b) separated diagonal gadgets
    for d in range(4):
        cs = [w for w in range(4) if w != d]
        for col in itertools.product((0, 1), repeat=3):
            sig = dict(zip(cs, col))
            seps = [w for w in cs if w != t and w in ctrl and sig[w] != x[w]]
            ok = any(w in pair for w in seps) or (d == t and seps and use_single_target)
            if not ok: continue
            gens.append([(1 - 2 * s[d]) % 4 if all(s[w] == sig[w] for w in cs) else 0 for s in ST])
    # (c) white units and CCZs on a pair wire
    for w in pair:
        for b in range(4):
            if b == w: continue
            gens.append([(1 if s[w] != x[w] else 0) * s[b] for s in ST])
        for b, e in itertools.combinations([v for v in range(4) if v != w], 2):
            gens.append([2 * (1 if s[w] != x[w] else 0) * s[b] * s[e] for s in ST])
    return gens

def fvec(d):
    v = [0] * N
    for k, val in d.items(): v[IDX[code(n, k)]] = (v[IDX[code(n, k)]] + val) % 4
    return v

bad = 0
for c in range(15):
    g = menu(c)
    t, x, pair, single = roles(c)
    out = []
    if 1 <= c and c + 2 <= 15:
        ok = hnf_member(g, fvec({c - 1: 1, c + 2: 3})); out.append(('bridge', ok)); bad += not ok
    for xx in range(16):
        if xx in (c, c + 1): continue
        ok = hnf_member(g, fvec({c: 1, c + 1: 1, xx: 2})); bad += not ok
        if not ok: out.append(('scalar', xx))
    print(c, 't', t, 'pair', pair, 'single', single, out)
print('bad', bad)

print('--- with the global phase, all bridge choices, one scalar per pair')
def menu2(a):
    return menu(a) + [[1] * N]
for c in range(15):
    g = menu2(c)
    br = [(x, y) for x in range(c) for y in range(c + 2, 16) if hnf_member(g, fvec({x: 1, y: 3}))]
    allbr = [(x, y) for x in range(c) for y in range(c + 2, 16)]
    sc = [x for x in range(16) if x not in (c, c + 1) and hnf_member(g, fvec({c: 1, c + 1: 1, x: 2}))]
    print(c, 'bridges ok', len(br), '/', len(allbr), br[:4], '| scalars ok', sc)
