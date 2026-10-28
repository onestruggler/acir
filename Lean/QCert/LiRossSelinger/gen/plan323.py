"""Subcase 3.2.3 on Fin 6 (c=4, d=5): derivations
   [K_ab'cd] S_r [K_0123]  ~  X [K'] Y [K_abcd] S_s
through the base K_13cd K_0123 K_23cd ~ K_012c (relation (5a))."""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(HERE, '..')
import itertools, json, sys, time
import numpy as np
from rules import N, X, K
from passtools import *
from sides2 import apply_all
from alg import ident as aident, word_apply

m = 6
def kmat(S):
    M = np.eye(m)
    a, b, c, d = S
    H = 0.5 * np.array([[1, 1, 1, 1], [1, -1, 1, -1], [1, 1, -1, -1], [1, -1, -1, 1]])
    idx = [a, b, c, d]
    for i in range(4):
        for j in range(4):
            M[idx[i], idx[j]] = H[i, j]
    return M
def spmat(A):
    M = np.zeros((m, m))
    for j, v in enumerate(A):
        M[abs(v) - 1, j] = 1 if v > 0 else -1
    return M
def mat_sp(M):
    img = []
    for j in range(m):
        col = M[:, j]
        nz = np.nonzero(np.abs(col) > 1e-9)[0]
        if len(nz) != 1 or abs(abs(col[nz[0]]) - 1) > 1e-9:
            return None
        img.append(int((nz[0] + 1) * (1 if col[nz[0]] > 0 else -1)))
    return tuple(img)
def wmat(w):
    M = np.eye(m)
    for g in w:
        if g[0] == 'k':
            M = M @ kmat(g[1:])
        else:
            M = M @ spmat(sp_of_gen(g, m))
    return M
ALLSP = []
for perm in itertools.permutations(range(m)):
    for sg in itertools.product([1, -1], repeat=m):
        ALLSP.append(tuple(sg[j] * (perm[j] + 1) for j in range(m)))
ALLSPM = np.array([spmat(A) for A in ALLSP])

KB = K(0, 1, 2, 3)
BASES = [((1, 3, 4, 5), (2, 3, 4, 5), [('rev_r5a', [0, 1, 2, 3, 4, 5], True, 0), ('r1c', [2, 3, 4, 5], True, 1)]),
         ((2, 3, 4, 5), (1, 3, 4, 5), [('r5a', [0, 1, 2, 3, 4, 5], True, 1), ('r1c', [2, 3, 4, 5], True, 0)])]

def plan(A, g1, g2, C):
    """Find X with  K_A g1 K_B g2 K_C = X K_L K_B K_R Y."""
    MA = kmat(A) @ wmat(g1)
    KBm = kmat((0, 1, 2, 3))
    G2 = wmat(g2)
    KCm = kmat(C)
    best = None
    for (L, R, fin) in BASES:
        KL, KR = kmat(L), kmat(R)
        # mu1 = KL X^T MA for all X at once
        mu1s = np.einsum('ij,njk,kl->nil', KL, ALLSPM.transpose(0, 2, 1), MA)
        for idx in range(len(ALLSP)):
            mu1 = mat_sp(mu1s[idx])
            if mu1 is None:
                continue
            mu2 = mat_sp(KBm @ mu1s[idx] @ KBm @ G2)
            if mu2 is None:
                continue
            Y = mat_sp(KR @ mu1s[idx] @ KBm @ G2 @ KCm) if False else mat_sp(KR @ spmat(mu2) @ KCm)
            if Y is None:
                continue
            Xw = word_of_sp(ALLSP[idx])
            Yw = word_of_sp(Y)
            cost = len(Xw) + len(Yw)
            if best is None or cost < best[0]:
                best = (cost, ALLSP[idx], mu1, mu2, Y, L, R, fin)
    return best

def derive(al, be, a, b, Sr, Ss):
    A, C = (al, be, 4, 5), (a, b, 4, 5)
    lhs = (K(*A),) + tuple(Sr) + (KB,)
    g1, g2 = tuple(Sr), tuple(reversed(Ss))
    best = plan(A, g1, g2, C)
    assert best is not None, ('no plan', A, C, Sr, Ss)
    cost, Xs, mu1, mu2, Y, L, R, fin = best
    Xw, mu1w, mu2w, Yw = word_of_sp(Xs), word_of_sp(mu1), word_of_sp(mu2), word_of_sp(Y)
    w = lhs
    steps = sp_derive((), g2 + tuple(Ss), m, off=len(w))
    w = apply_all(w, steps)
    st = [('r1c', list(C), False, len(lhs) + len(g2))]
    w = apply_all(w, st); steps += st
    # w = K_A g1 K_B g2 K_C K_C Ss
    # refactor K_A: () K_A g1 -> Xw K_L mu1w
    st, w = refactor(w, 0, 0, 1 + len(g1), Xw, L, mu1w, m); steps += st
    kb = len(Xw) + 1 + len(mu1w)
    st, w = refactor(w, len(Xw) + 1, kb, kb + 1 + len(g2), (), (0, 1, 2, 3), mu2w, m); steps += st
    kc = len(Xw) + 2 + len(mu2w)
    st, w = refactor(w, len(Xw) + 2, kc, kc + 1, (), R, Yw, m); steps += st
    p = len(Xw)
    for (f, ps, d, o) in fin:
        stp = [(f, ps, d, p + o)]
        w = apply_all(w, stp); steps += stp
    P = tuple(Xw) + (K(0, 1, 2, 4),) + tuple(Yw)
    rhs = P + (K(*C),) + tuple(Ss)
    assert w == rhs, (w, rhs)
    return P, steps

if __name__ == '__main__':
    cfgs = [((0, 1), (0, 2)), ((0, 1), (1, 3)), ((0, 2), (0, 1)), ((0, 2), (2, 3)), ((0, 3), (0, 3)),
            ((0, 3), (1, 2)), ((1, 2), (0, 3)), ((1, 2), (1, 2)), ((1, 3), (0, 1)), ((1, 3), (2, 3)),
            ((2, 3), (0, 2)), ((2, 3), (1, 3))]
    res = {}
    for (ab, ab2) in cfgs:
        a, b = ab; al, be = ab2
        for bits in [bb + (0, 0) for bb in itertools.product([0, 1], repeat=4)]:
            x, y, p, q, z, u = bits
            Sr = tuple(g for g, t in ((N(al), x), (N(be), y), (N(4), z), (N(5), u)) if t)
            Ss = tuple(g for g, t in ((N(a), p), (N(b), q), (N(4), z), (N(5), u)) if t)
            t0 = time.time()
            try:
                P, st = derive(al, be, a, b, Sr, Ss)
            except AssertionError as e:
                continue
            key = '%d%d%d%d_%s' % (a, b, al, be, ''.join(map(str, bits)))
            res[key] = (P, st)
            print(key, len(P), len(st), round(time.time() - t0, 2)); sys.stdout.flush()
    json.dump(res, open(os.path.join(HERE, 'd323.json'), 'w'))
    print(len(res))
