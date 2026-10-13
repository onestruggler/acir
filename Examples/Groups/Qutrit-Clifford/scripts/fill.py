"""Fill the loops of the three-qutrit box relations by translates of the
loops of C15-C18 (BFS over loops, moves: replace an arc of a cell by the
rest of the cell, remove spurs)."""
import sys, itertools, pickle, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from geo import *

# SL(2,3) and the stabiliser of the base edge
SL2 = [((a, b), (c, d)) for a in range(3) for b in range(3) for c in range(3) for d in range(3)
       if (a * d - b * c) % 3 == 1]
assert len(SL2) == 24

def local(m0, m1, m2):
    M = [[0] * 6 for _ in range(6)]
    for w, m in enumerate((m0, m1, m2)):
        # coordinates (x_w, z_w) at indices w, 3+w
        idx = (w, 3 + w)
        for i in range(2):
            for j in range(2):
                M[idx[i]][idx[j]] = m[i][j]
    return tuple(tuple(r) for r in M)

STAB = [local(a, b, c) for a in SL2 for b in SL2 for c in SL2]

def hyp_pair(plane):
    """A basis (e, f) of a hyperbolic plane with form(e, f) = 1."""
    u, v = plane
    s = form(u, v)
    assert s != 0
    return u, tuple((x * (1 if s == 1 else 2)) % 3 for x in v)

def complement(vecs):
    """Basis of the symplectic complement of the span of vecs."""
    sols = []
    for v in itertools.product(range(3), repeat=6):
        if any(v) and all(form(u, v) == 0 for u in vecs):
            sols.append(v)
    return rref(sols)

_comp = {}
def to_edge(pa, pb):
    """g in Sp(6,3) with g V2 = pa and g V0 = pb."""
    k = (pa, pb)
    if k in _comp:
        return _comp[k]
    e2, f2 = hyp_pair(pa)
    e0, f0 = hyp_pair(pb)
    c = complement(list(pa) + list(pb))
    e1, f1 = hyp_pair(c)
    cols = {0: e0, 3: f0, 1: e1, 4: f1, 2: e2, 5: f2}
    g = tuple(tuple(cols[j][i] for j in range(6)) for i in range(6))
    assert img(g, V2) == pa and img(g, V0) == pb
    _comp[k] = (g, minv(g))
    return _comp[k]

def edge_frame(v0, v1):
    """g, g^-1 with g (base edge) = (v0, v1), oriented by type."""
    if v0[0] == 'A':
        return to_edge(v0[1], v1[1])
    return to_edge(v1[1], v0[1])

def norm_seq(seq):
    g, gi = edge_frame(seq[0], seq[1])
    return [(t, img(gi, p)) for (t, p) in seq]

# ---------------------------------------------------------------- relators
def relator_loops():
    from rules import RULES
    out = []
    for name in ('C15', 'C16', 'C17', 'C18'):
        n, l, r = RULES[name]
        verts, bl = loop_of(l + inv_word(r))
        out.append((name, verts))
    return out

def rotations(rels):
    rots = []
    for name, verts in rels:
        m = len(verts)
        for s in range(m):
            for d in (1, -1):
                seq = [verts[(s + d * j) % m] for j in range(m)]
                rots.append((name, s, d, norm_seq(seq)))
    return rots

def build_index(rots):
    """For each rotation: map image of nr2 under STAB -> list of stab indices."""
    idx = []
    cache = {}
    for (name, s, d, nr) in rots:
        p2 = nr[2]
        if p2 not in cache:
            dct = {}
            for i, M in enumerate(STAB):
                q = img(M, p2[1])
                dct.setdefault(q, []).append(i)
            cache[p2] = dct
        idx.append(cache[p2])
    return idx

# ---------------------------------------------------------------- moves
def canon(loop):
    if not loop:
        return ()
    m = len(loop)
    best = None
    for s in range(m):
        t = tuple(loop[s:] + loop[:s])
        if best is None or t < best:
            best = t
    return best

def unspur(loop):
    loop = list(loop)
    changed = True
    while changed and len(loop) >= 2:
        changed = False
        m = len(loop)
        if m == 2:
            return []
        for i in range(m):
            if loop[(i - 1) % m] == loop[(i + 1) % m]:
                # remove loop[i] and loop[i+1]
                a, b = i, (i + 1) % m
                loop = [loop[k] for k in range(m) if k not in (a, b)]
                changed = True
                break
    return loop

def moves(loop, rots, idx, minp=2):
    m = len(loop)
    out = []
    for i in range(m):
        for (ri, (name, s, d, nr)) in enumerate(rots):
            L = len(nr)
            if nr[0][0] != loop[i][0]:
                continue
            g, gi = edge_frame(loop[i], loop[(i + 1) % m])
            w2 = img(gi, loop[(i + 2) % m][1])
            if loop[(i + 2) % m][0] != nr[2][0]:
                continue
            cands = idx[ri].get(w2, [])
            if not cands:
                continue
            seen = set()
            for si in cands:
                S_ = STAB[si]
                # extend the match as far as possible
                p = 2
                while p + 1 < L and p + 1 <= m - 1:
                    nxt = loop[(i + p + 1) % m]
                    if nxt[0] != nr[p + 1][0]:
                        break
                    if img(gi, nxt[1]) != img(S_, nr[p + 1][1]):
                        break
                    p += 1
                for pp in range(minp, p + 1):
                    # complement path: c_{L-1}, ..., c_{pp+1}
                    gs = mmul(g, S_)
                    comp = tuple((nr[j][0], img(gs, nr[j][1])) for j in range(L - 1, pp, -1))
                    key_ = (pp, comp)
                    if key_ in seen:
                        continue
                    seen.add(key_)
                    new = [loop[i]] + list(comp) + [loop[(i + pp + k) % m] for k in range(0, m - pp)]
                    # new starts at loop[i]; the arc loop[i..i+pp] replaced
                    # by comp; then loop[i+pp], ..., loop[i-1]
                    new = new[:1 + len(comp)] + [loop[(i + pp + k) % m] for k in range(0, m - pp)]
                    out.append(((i, name, s, d, si, pp), new))
    return out

def search(loop0, rots, idx, maxlen=10, maxnodes=20000):
    start = canon(unspur(loop0))
    if not start:
        return []
    from collections import deque
    prev = {start: None}
    q = deque([start])
    while q:
        cur = q.popleft()
        for (mv, new) in moves(list(cur), rots, idx):
            new = unspur(new)
            if len(new) > maxlen:
                continue
            c = canon(new)
            if c in prev:
                continue
            prev[c] = (cur, mv)
            if not c:
                path = []
                x = c
                while prev[x] is not None:
                    path.append(prev[x][1])
                    x = prev[x][0]
                return path[::-1]
            if len(prev) > maxnodes:
                return None
            q.append(c)
    return None

if __name__ == '__main__':
    from boxrel import R
    t0 = time.time()
    rels = relator_loops()
    rots = rotations(rels)
    idx = build_index(rots)
    print('index built', time.time() - t0, 'rots', len(rots), flush=True)
    which = sys.argv[1] if len(sys.argv) > 1 else None
    res = {}
    for (fig, name, n, l, r) in R:
        if n != 3:
            continue
        if which and not name.startswith(which):
            continue
        w = l + inv_word(r)
        verts, bl = loop_of(w)
        t1 = time.time()
        path = search(verts, rots, idx)
        res[name] = path
        print(fig, name, len(verts), None if path is None else len(path),
              None if path is None else [(m[1], m[5]) for m in path], round(time.time() - t1, 1), flush=True)
