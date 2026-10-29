from chain import *
from lib import *

def commutes(x, y):
    return disjoint(x, y) or (x[0] == 'Z' and y[0] == 'Z')

def cancel_waypoints(w):
    w = list(w); out = []
    while w:
        best = None
        for i in range(len(w)):
            for j in range(i + 1, len(w)):
                if w[i] == w[j] and all(commutes(w[i], w[k]) for k in range(i + 1, j)):
                    if best is None or j - i < best[1] - best[0]: best = (i, j)
                    break
        if best is None: raise ValueError('no cancel ' + str(w))
        i, j = best
        w = w[:i] + w[i + 1:j] + w[j + 1:]
        out.append(list(w))
    return out

def strip(u, v):
    p = 0
    while p < min(len(u), len(v)) and u[p] == v[p]: p += 1
    q = 0
    while q < min(len(u), len(v)) - p and u[len(u) - 1 - q] == v[len(v) - 1 - q]: q += 1
    return p, q

def solve(N, u, v, lib, K, rules=(), depth=4, exts=(0, 1, 2)):
    e = find_ext(u, v, rules)
    if e:
        name, pos, fwd = e
        A, B = [(r[1], r[2]) for r in rules if r[0] == name][0]
        if not fwd: A, B = B, A
        return [('ext', pos, A, B, name, fwd)]
    p, q = strip(u, v)
    um, vm = u[p:len(u) - q], v[p:len(v) - q]
    if len(supp(um) | supp(vm)) <= K:
        return [('sem', p, list(um), list(vm))]
    st = steps_between(N, u, v, K, comm=False)
    if st is not None and len(st) <= 3:
        return st
    for ex in exts:
        pp, qq = max(0, p - ex), max(0, q - ex)
        um, vm = u[pp:len(u) - qq], v[pp:len(v) - qq]
        st = bfs(N, um, vm, lib, K, depth=depth)
        if st is not None:
            return [(k, pos + pp, W, R) for (k, pos, W, R) in st]
    return None

def solve_chain(N, lines, lib, K, rules=(), depth=4):
    allsteps = []
    for i in range(len(lines) - 1):
        u, v = lines[i], lines[i + 1]
        st = solve(N, u, v, lib, K, rules, depth)
        if st is None:
            print('FAIL at', i); return None, i
        cur = list(u)
        for s in st:
            k, pos, W, R = s[:4]
            assert cur[pos:pos + len(W)] == list(W), (i, s)
            if k == 'sem': assert len(supp(W) | supp(R)) <= K and eq(N, W, R)
            cur = cur[:pos] + list(R) + cur[pos + len(W):]
        assert cur == list(v)
        allsteps += st
    return allsteps, None
