# Construction (6) at n = 4: [V, W] = G with det V, det W in {+-1}, so
# that L_{C1}(V) and L_{C2}(W) with one idle wire each are circuits.
# G = L_u(K_w) . (-i at u=0, w=0) on wires (u, w) = (0, 1).
import sys
DEPTH = int(sys.argv[1]) if len(sys.argv) > 1 else 5
sys.argv = ['tDec6', '2']
exec(open('tDec.py').read().split("allok = True")[0])   # the definitions, at n = 2

u, w = 0, 1
Gm = ctrl([u], [w], K2) * phase_on(lambda x: x[u] == 0 and x[w] == 0, MI)

def det(Mx):
    # 4 x 4 over Q, Laplace
    bits = [(0, 0), (0, 1), (1, 0), (1, 1)]
    A = [[Mx.d[r].get(c, ZERO) for c in bits] for r in bits]
    def d(A):
        if len(A) == 1: return A[0][0]
        tot = ZERO
        for j in range(len(A)):
            minor = [row[:j] + row[j + 1:] for row in A[1:]]
            term = A[0][j] * d(minor)
            tot = tot + term if j % 2 == 0 else tot - term
        return tot
    return d(A)

two = {
    'S0': ctrl([], [u], S2), 'S1': ctrl([], [w], S2),
    'K0': ctrl([], [u], K2), 'K1': ctrl([], [w], K2),
    'CS': ctrl([u], [w], S2),
    'X0': ctrl([], [u], X2), 'X1': ctrl([], [w], X2),
    'CX01': ctrl([u], [w], X2), 'CX10': ctrl([w], [u], X2),
}
pm1 = {ONE, NEG}
depth = DEPTH
frontier = [((), M.ident())]
pool = {}
for _ in range(depth):
    nxt = []
    for wd, Mx in frontier:
        for g, Mg in two.items():
            Mn = Mx * Mg
            key = tuple(sorted((x, tuple(sorted(r.items(), key=repr))) for x, r in Mn.d.items()))
            if key in pool: continue
            pool[key] = (wd + (g,), Mn)
            nxt.append((wd + (g,), Mn))
    frontier = nxt
cands = [(wd, Mx) for wd, Mx in pool.values() if det(Mx) in pm1]
print(f'{len(pool)} words, {len(cands)} with det +-1', flush=True)
found = []
for wV, V in cands:
    Vi = V.inv()
    L = V * Gm * Vi    # want L = G? no: [V,W] = G  <=>  V W V^-1 = G W  <=> W = V^-1 G W V ... search directly
    for wW, Wm in cands:
        if V * Wm * Vi * Wm.inv() == Gm:
            found.append((wV, wW))
            if len(found) >= 5: break
    if len(found) >= 5: break
print('found:', found, flush=True)
