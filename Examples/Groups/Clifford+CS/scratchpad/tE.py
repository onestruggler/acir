# The letter-level encoding at width 4: each gate's encoding, spelled
# over P'-letters (not raw two-level generators), equals the gate.
#   quad a b c d = pp[a,b] pp[b,c] pp[b,c] pp[d,c]      ( = i_a i_b i_c i_d )
#   kpair p q    = KKb[p,q] . iquad-correction          ( = K_p K_q ),
# since K_q^2 = (i_c i_d)^-1 (rel-16), so K_p K_q = KKb[p,q] . K_q^2^-1^-1
# ... concretely K_p K_q = KKb[p,q] . (K_q)^2 and (K_q)^2 = i_c^-1 i_d^-1.
import csP
from itertools import combinations

N = 16
n = 4

def pp(a, b):
    return csP.matmul(csP.two_level(N, 'i', a), csP.minv('i', N, b))
def kkb(a, b, c, d):
    return csP.matmul(csP.two_level(N, 'K', min(a,b), max(a,b)),
                      csP.minv('K', N, min(c,d), max(c,d)))
E = csP.ident(N)
def mp(*Ms):
    R = E
    for M in Ms: R = csP.matmul(R, M)
    return R
def eq(A, B): return csP.key(A) == csP.key(B)

def quad(a, b, c, d):          # i_a i_b i_c i_d
    return mp(pp(a, b), pp(b, c), pp(b, c), pp(d, c))
def iquad_inv(a, b, c, d):     # i_a^-1 i_b^-1 i_c^-1 i_d^-1
    return mp(pp(b, a), pp(c, b), pp(c, b), pp(c, d))
def kpair(p, q):               # K_p K_q  (p, q disjoint sorted pairs)
    # K_q^2 = i_q0^-1 i_q1^-1 : so K_p K_q = KKb[p,q] . K_q^2, and the
    # corrections across a whole product collect into inverse quads.
    half = csP.matmul(csP.minv('i', N, q[0]), csP.minv('i', N, q[1]))
    return mp(kkb(p[0], p[1], q[0], q[1]), half)

ok = True
# the quad spelling
ok &= eq(quad(3, 5, 8, 14),
         mp(*(csP.two_level(N, 'i', x) for x in (3, 5, 8, 14))))
# the K-pair spelling
ok &= eq(kpair((0, 1), (2, 3)),
         mp(csP.two_level(N, 'K', 0, 1), csP.two_level(N, 'K', 2, 3)))
print('spellings:', 'OK' if ok else 'FAIL')

# letter-level encodings of the gates
def Egate_S(w):
    xs = [x for x in range(N) if (x >> w) & 1]
    M = E
    for j in range(0, len(xs), 4):
        M = csP.matmul(M, quad(*xs[j:j+4]))
    return M
def Egate_CS(v, w):
    xs = [x for x in range(N) if (x >> v) & 1 and (x >> w) & 1]
    return quad(*xs)
def Egate_iI():
    M = E
    xs = list(range(N))
    for j in range(0, N, 4):
        M = csP.matmul(M, quad(*xs[j:j+4]))
    return M
def Egate_K(w):
    prs = [(y, y | (1 << w)) for y in range(N) if not (y >> w) & 1]
    M = E
    corr = []
    for j in range(0, len(prs), 2):
        M = csP.matmul(M, kkb(*prs[j], *prs[j + 1]))
        corr.extend(prs[j + 1])
    # the collected corrections: prod K_q^2 = prod i_x^-1 over the odd
    # pairs' indices, in inverse quads
    for j in range(0, len(corr), 4):
        M = csP.matmul(M, iquad_inv(*corr[j:j+4]))
    return M

import csP as _
# reference gate matrices (from csP.py esem, re-derived)
def gate_S_ref(w):
    M = E
    for y in range(N):
        if (y >> w) & 1: M = csP.matmul(M, csP.two_level(N, 'i', y))
    return M
def gate_K_ref(w):
    M = E
    for y in range(N):
        if not (y >> w) & 1: M = csP.matmul(M, csP.two_level(N, 'K', y, y | (1 << w)))
    return M

allok = True
for w in range(n):
    allok &= eq(Egate_S(w), gate_S_ref(w))
    allok &= eq(Egate_K(w), gate_K_ref(w))
for v, w in combinations(range(n), 2):
    xs = [x for x in range(N) if (x >> v) & 1 and (x >> w) & 1]
    ref = E
    for x in xs: ref = csP.matmul(ref, csP.two_level(N, 'i', x))
    allok &= eq(Egate_CS(v, w), ref)
ref = E
for x in range(N): ref = csP.matmul(ref, csP.two_level(N, 'i', x))
allok &= eq(Egate_iI(), ref)
print('letter-level encodings at width 4:', 'OK' if allok else 'FAIL')
