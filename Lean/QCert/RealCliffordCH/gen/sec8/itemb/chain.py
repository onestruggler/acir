"""Chain builder: split transitions between consecutive words into steps
(sem windows on <= K indices, commutations of disjoint pairs, ext rules)."""
import re
from collections import deque
import numpy as np
from core import *

def parse(sline):
    out = []
    for m in re.finditer(r'(𝐻|𝑋|\(−1\))\[(\d+)(?:,(\d+))?\]', sline):
        k, a, b = m.group(1), int(m.group(2)), m.group(3)
        if k == '(−1)': out.append(Z(a))
        elif k == '𝐻': out.append(H(a, int(b)))
        else: out.append(X(a, int(b)))
    return out

def prefixes(N, w):
    P = [np.eye(N)]
    for g in w: P.append(P[-1] @ gmat(N, g))
    return P

def disjoint(x, y):
    return not (set(x[1:]) & set(y[1:]))

def split(N, u, v, K, comm=True):
    """Blocks (i,i2,j,j2,kind) turning u into v; kind 'id','sem','comm'."""
    Pu, Pv = prefixes(N, u), prefixes(N, v)
    match = {}
    for i in range(len(u) + 1):
        for j in range(len(v) + 1):
            match[(i, j)] = np.allclose(Pu[i], Pv[j])
    # BFS minimizing number of non-id blocks
    start, goal = (0, 0), (len(u), len(v))
    best = {start: (0, None)}
    dq = deque([start])
    order = []
    while dq:
        st = dq.popleft()
        i, j = st
        cost = best[st][0]
        cands = []
        if i < len(u) and j < len(v) and u[i] == v[j]:
            cands.append(((i + 1, j + 1), 'id', 0))
        if comm and i + 2 <= len(u) and j + 2 <= len(v) and u[i] == v[j + 1] and u[i + 1] == v[j] \
                and disjoint(u[i], u[i + 1]) and u[i] != u[i + 1]:
            cands.append(((i + 2, j + 2), 'comm', 1))
        for i2 in range(i, len(u) + 1):
            if len(supp(u[i:i2])) > K: break
            for j2 in range(j, len(v) + 1):
                if (i2, j2) == (i, j): continue
                if len(supp(u[i:i2]) | supp(v[j:j2])) > K: break
                if match[(i2, j2)]:
                    cands.append(((i2, j2), 'sem', 1))
        for nst, kind, c in cands:
            nc = cost + c
            if nst not in best or best[nst][0] > nc:
                best[nst] = (nc, (st, kind))
                if c == 0: dq.appendleft(nst)
                else: dq.append(nst)
    if goal not in best: return None
    blocks = []
    st = goal
    while st != start:
        prev, kind = best[st][1]
        blocks.append((prev[0], st[0], prev[1], st[1], kind))
        st = prev
    blocks.reverse()
    # merge consecutive id blocks away
    return [b for b in blocks if b[4] != 'id']

def steps_between(N, u, v, K, comm=True):
    blocks = split(N, u, v, K, comm)
    if blocks is None: return None
    steps = []
    cur = list(u)
    for (i, i2, j, j2, kind) in blocks:
        # current word = v[:j] + u[j?]... positions: before block, the prefix is v[:j]
        pos = j
        W, R = u[i:i2], v[j:j2]
        assert cur[pos:pos + len(W)] == W, (cur, pos, W)
        cur = cur[:pos] + R + cur[pos + len(W):]
        steps.append((kind, pos, W, R))
    assert cur == v
    return steps

def find_ext(u, v, rules):
    """u -> v by one ext rule application (rules: list of (name, L, R))."""
    for name, L, R in rules:
        for fwd, (A, B) in ((True, (L, R)), (False, (R, L))):
            for p in range(len(u) - len(A) + 1):
                if u[p:p + len(A)] == A and u[:p] + B + u[p + len(A):] == v:
                    return (name, p, fwd)
    return None

def comm_nbrs(w):
    for i in range(len(w) - 1):
        if w[i] != w[i + 1] and disjoint(w[i], w[i + 1]):
            yield i, tuple(w[:i]) + (w[i + 1], w[i]) + tuple(w[i + 2:])

def comm_ball(w, d):
    """words reachable by <= d commutations, with paths (list of positions)."""
    seen = {tuple(w): []}
    frontier = [tuple(w)]
    for _ in range(d):
        nf = []
        for x in frontier:
            for i, y in comm_nbrs(x):
                if y not in seen:
                    seen[y] = seen[x] + [i]
                    nf.append(y)
        frontier = nf
    return seen

def transition(N, u, v, K, d=3):
    """Steps u -> v: commutations on u side, DP blocks, commutations on v side (reversed)."""
    st = steps_between(N, u, v, K)
    if st is not None: return st
    bu, bv = comm_ball(u, d), comm_ball(v, d)
    best = None
    for x, px in sorted(bu.items(), key=lambda t: len(t[1])):
        for y, py in sorted(bv.items(), key=lambda t: len(t[1])):
            if best is not None and len(px) + len(py) >= best[0]: break
            s = steps_between(N, list(x), list(y), K)
            if s is not None:
                cost = len(px) + len(py) + len(s)
                if best is None or cost < best[0]:
                    best = (cost, px, s, py, x, y)
    if best is None: return None
    _, px, s, py, x, y = best
    steps = []
    cur = list(u)
    for i in px:
        steps.append(('comm', i, cur[i:i + 2], [cur[i + 1], cur[i]]))
        cur[i], cur[i + 1] = cur[i + 1], cur[i]
    steps += s
    # v side: y reached from v by py; undo from y back to v
    cur = list(y)
    path = []
    w = list(v)
    states = [list(v)]
    for i in py:
        w = w[:]; w[i], w[i + 1] = w[i + 1], w[i]; states.append(w)
    for k in range(len(py) - 1, -1, -1):
        i = py[k]
        a = states[k + 1]
        steps.append(('comm', i, a[i:i + 2], [a[i + 1], a[i]]))
    return steps

def transition2(N, u, v, K, d=3, ext=0):
    """Strip common prefix/suffix (keeping `ext` extra letters), then transition on middles."""
    p = 0
    while p < min(len(u), len(v)) and u[p] == v[p]: p += 1
    q = 0
    while q < min(len(u), len(v)) - p and u[len(u) - 1 - q] == v[len(v) - 1 - q]: q += 1
    p = max(0, p - ext); q = max(0, q - ext)
    um, vm = u[p:len(u) - q], v[p:len(v) - q]
    st = transition(N, um, vm, K, d)
    if st is None: return None
    return [(k, pos + p, W, R) for (k, pos, W, R) in st]

def check_steps(N, u, v, steps, K, rules=()):
    cur = list(u)
    for st in steps:
        k, pos, W, R = st[0], st[1], st[2], st[3]
        assert cur[pos:pos + len(W)] == list(W), (st, cur)
        if k == 'sem':
            assert len(supp(W) | supp(R)) <= K and eq(N, W, R), st
        elif k == 'comm':
            assert len(W) == 2 and W[0] == R[1] and W[1] == R[0] and disjoint(W[0], W[1])
        cur = cur[:pos] + list(R) + cur[pos + len(W):]
    assert cur == list(v)
    return True
