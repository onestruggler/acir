"""BFS with a library of short identities on <= K indices."""
import itertools
from collections import defaultdict, deque
import numpy as np
from core import *
from chain import disjoint

def letters(m):
    L = [Z(a) for a in range(m)]
    for a in range(m):
        for b in range(a + 1, m):
            L += [X(a, b), H(a, b)]
    return L

def key(N, w):
    M = wmat(N, w)
    return tuple(np.round(M, 6).flatten())

def build_lib(m, K, maxlen=3):
    groups = defaultdict(list)
    Ls = letters(m)
    for l in range(0, maxlen + 1):
        for w in itertools.product(Ls, repeat=l):
            if len(supp(w)) > K: continue
            groups[key(m, w)].append(w)
    return groups

def moves(N, w, lib, K, maxlen=3):
    w = tuple(w)
    out = []
    for i in range(len(w) + 1):
        for l in range(0, maxlen + 1):
            if i + l > len(w): break
            W = w[i:i + l]
            sW = supp(W)
            if len(sW) > K: continue
            for R in lib.get(key(N, W), []):
                if R == W: continue
                if len(sW | supp(R)) > K: continue
                if l == 0 and len(R) == 0: continue
                nw = w[:i] + R + w[i + l:]
                kind = 'comm' if (l == 2 and len(R) == 2 and R == (W[1], W[0]) and disjoint(W[0], W[1])) else 'sem'
                out.append((nw, (kind, i, list(W), list(R))))
    # 4-index commutations of disjoint pairs
    for i in range(len(w) - 1):
        if w[i] != w[i + 1] and disjoint(w[i], w[i + 1]) and len(supp(w[i:i + 2])) > K:
            nw = w[:i] + (w[i + 1], w[i]) + w[i + 2:]
            out.append((nw, ('comm', i, [w[i], w[i + 1]], [w[i + 1], w[i]])))
    return out

def bfs(N, u, v, lib, K, depth=4, maxlen=3, cap=200000):
    u, v = tuple(u), tuple(v)
    if u == v: return []
    fu = {u: None}; fv = {v: None}
    qu, qv = [u], [v]
    def path(f, x):
        p = []
        while f[x] is not None:
            prev, st = f[x]; p.append(st); x = prev
        return p[::-1]
    for d in range(depth):
        for side in (0, 1):
            f, q, other = (fu, qu, fv) if side == 0 else (fv, qv, fu)
            nq = []
            for x in q:
                for y, st in moves(N, x, lib, K, maxlen):
                    if y in f: continue
                    if len(y) > len(u) + 6 or len(y) > len(v) + 6: continue
                    f[y] = (x, st); nq.append(y)
                    if y in other:
                        a = path(fu, y); b = path(fv, y)
                        # reverse b: steps from y back to v
                        rb = []
                        for (k, i, W, R) in reversed(b):
                            rb.append((k, i, R, W))
                        return a + rb
                    if len(f) > cap: break
            if side == 0: qu = nq
            else: qv = nq
    return None
