"""Compact presentations of finite matrix groups (relations of short words), checked by
Todd–Coxeter."""
import itertools
import numpy as np
from collections import deque
from qc import key
from tcpp import index


def bfs(letters, mats, n):
    e = np.eye(n, dtype=complex)
    nf = {key(e): ()}
    el = {(): e}
    dq = deque([()])
    while dq:
        w = dq.popleft()
        m = el[w]
        for a in letters:
            p = m @ mats[a]
            k = key(p)
            if k not in nf:
                nf[k] = w + (a,)
                el[w + (a,)] = p
                dq.append(w + (a,))
    return nf


def matw(w, mats, n):
    r = np.eye(n, dtype=complex)
    for a in w:
        r = r @ mats[a]
    return r


def compact(letters, mats, n=8, maxdepth=6, verbose=False):
    nf = bfs(letters, mats, n)
    order = len(nf)
    rels = []
    seen = set()
    def add(u):
        v = nf[key(matw(u, mats, n))]
        if v != u and (u, v) not in seen:
            seen.add((u, v))
            rels.append((u, v))
    # powers up to the order of each letter
    for a in letters:
        m = np.eye(n, dtype=complex)
        for k in range(1, 30):
            m = m @ mats[a]
            add((a,) * k)
            if key(m) == key(np.eye(n)):
                break
    for depth in range(2, maxdepth + 1):
        for u in itertools.product(letters, repeat=depth):
            # only words all of whose proper subwords are normal forms
            if all(nf[key(matw(u[i:j], mats, n))] == u[i:j] for i in range(depth) for j in range(i + 1, depth + 1) if (i, j) != (0, depth)):
                add(u)
        got = index(letters, rels, maxcos=max(200000, 20 * order))
        if verbose:
            print('   depth', depth, 'rels', len(rels), 'index', got, 'order', order, flush=True)
        if got == order:
            return rels, order
    raise ValueError('no compact presentation')
