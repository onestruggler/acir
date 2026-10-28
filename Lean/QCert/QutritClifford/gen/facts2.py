"""Two-wire derivations with free one-wire segments (completeness on one
wire), for the stabiliser facts of the width-2 coset table.

A two-wire word (time order, letters H0 S0 H1 S1 CZ) is reduced to its
layers: the local elements between consecutive CZ letters, each a pair of
one-wire elements (projective, indices into the 216-element group).  A
rule l = r of (C6)-(C14) applies at the i-th CZ when the inner layers of l
equal the corresponding layers of the word; the outer layers are absorbed
into the neighbouring layers.  A bidirectional breadth-first search finds a
chain of rule applications, which `replay` turns into explicit words for
engine.Engine(2, ...).
"""
from collections import deque
import cliff
import qc
import cosets
import engine

ONE = cliff.bfs_words(1)
KEYS = list(ONE.keys())
IDX = {k: i for i, k in enumerate(KEYS)}
WORD1 = [[g for (g, _) in ONE[k]] for k in KEYS]
MUL = [[IDX[cliff.compose(KEYS[i], KEYS[j])] for j in range(len(KEYS))] for i in range(len(KEYS))]
E1 = IDX[cliff.ident(1)]
INV = [next(j for j in range(len(KEYS)) if MUL[i][j] == E1) for i in range(len(KEYS))]


def mul(l, m):
    return (MUL[l[0]][m[0]], MUL[l[1]][m[1]])


def inv(l):
    return (INV[l[0]], INV[l[1]])


IDL = (E1, E1)


def layer_of(seg):
    w0 = [(g, 0) for (g, j) in seg if j == 0]
    w1 = [(g, 0) for (g, j) in seg if j == 1]
    return (IDX[cliff.key(w0, 1)], IDX[cliff.key(w1, 1)])


def reduce(w):
    layers, cur = [], []
    for l in w:
        if l[0] == 'CZ':
            layers.append(layer_of(cur))
            cur = []
        else:
            cur.append(l)
    layers.append(layer_of(cur))
    return tuple(layers)


def word_of_layer(l):
    return [(g, 0) for g in WORD1[l[0]]] + [(g, 1) for g in WORD1[l[1]]]


def word_of(layers):
    out = []
    for i, l in enumerate(layers):
        if i:
            out.append(('CZ', 0))
        out += word_of_layer(l)
    return out


class Rule:
    def __init__(self, name, l, r):
        self.name, self.l, self.r = name, reduce(l), reduce(r)
        self.lw, self.rw = l, r


def apply(state, rule, i, rev):
    """Apply rule at CZ index i (the rule's first CZ on the word's i-th);
    None if the inner layers do not match."""
    l, r = (rule.r, rule.l) if rev else (rule.l, rule.r)
    s = len(l) - 1          # CZ letters in l
    if s == 0 or i + s > len(state) - 1:
        return None
    for j in range(1, s):
        if state[i + j] != l[j]:
            return None
    X = mul(state[i], inv(l[0]))
    Y = mul(inv(l[s]), state[i + s])
    mid = list(r)
    if len(mid) == 1:
        new = [mul(mul(X, mid[0]), Y)]
    else:
        mid[0] = mul(X, mid[0])
        mid[-1] = mul(mid[-1], Y)
        new = mid
    out = list(state[:i]) + new + list(state[i + s + 1:])
    return tuple(out)


def norm(state):
    return (IDL,) + tuple(state[1:])


def search(rules, start, goal, maxcz=6, maxdepth=8):
    """Bidirectional search; states normalised in their first layer."""
    fwd = {norm(start): None}
    bwd = {norm(goal): None}
    fq, bq = [norm(start)], [norm(goal)]
    for depth in range(maxdepth):
        for (seen, q, other, back) in ((fwd, fq, bwd, False), (bwd, bq, fwd, True)):
            nq = []
            for st in q:
                for ri, rule in enumerate(rules):
                    for rev in (False, True):
                        for i in range(len(st) - 1):
                            ns = apply(st, rule, i, rev)
                            if ns is None or len(ns) - 1 > maxcz:
                                continue
                            ns = norm(ns)
                            if ns in seen:
                                continue
                            seen[ns] = (st, ri, i, rev)
                            if ns in other:
                                return path(fwd, bwd, ns)
                            nq.append(ns)
            q[:] = nq
    return None


def path(fwd, bwd, meet):
    steps = []
    s = meet
    while fwd[s] is not None:
        st, ri, i, rev = fwd[s]
        steps.append((st, ri, i, rev))
        s = st
    steps.reverse()
    back = []
    s = meet
    while bwd[s] is not None:
        st, ri, i, rev = bwd[s]
        back.append((s, ri, i, not rev))     # from s to st
        s = st
    return steps, back



def split_layers(w):
    """The literal layers of a word, each ordered wire 0 first."""
    layers, cur = [], []
    for l in w:
        if l[0] == 'CZ':
            layers.append(cur)
            cur = []
        else:
            cur.append(l)
    layers.append(cur)
    return [[l for l in L if l[1] == 0] + [l for l in L if l[1] == 1] for L in layers]


def join(layers):
    out = []
    for i, L in enumerate(layers):
        if i:
            out.append(('CZ', 0))
        out += L
    return out


def lw(l):
    """The canonical word of a layer element, wire 0 first."""
    return word_of_layer(l)


def morph(layers, j, new):
    """Words taking layer j to the word new: first its wire-0 part, then
    its wire-1 part (each one free step)."""
    old = layers[j]
    o0 = [l for l in old if l[1] == 0]
    n0 = [l for l in new if l[1] == 0]
    n1 = [l for l in new if l[1] == 1]
    mid = list(layers)
    mid[j] = n0 + [l for l in old if l[1] == 1]
    out = [join(mid)]
    fin = list(layers)
    fin[j] = n0 + n1
    out.append(join(fin))
    return out, fin


def replay(rules, start, steps):
    """Explicit words for a chain of reduced rule applications from the
    word start."""
    lay = list(reduce(start))
    words = [list(start)]
    cur_lit = split_layers(start)
    # canonicalise the start
    for j in range(len(cur_lit)):
        ws, cur_lit = morph(cur_lit, j, lw(lay[j]))
        words += ws
    for (ri, i, rev) in steps:
        rule = rules[ri]
        lwd, rwd = (rule.rw, rule.lw) if rev else (rule.lw, rule.rw)
        Ll, Lr = split_layers(lwd), split_layers(rwd)
        lred, rred = (rule.r, rule.l) if rev else (rule.l, rule.r)
        s = len(Ll) - 1
        X = mul(lay[i], inv(lred[0]))
        Y = mul(inv(lred[s]), lay[i + s])
        # expose the rule's left side
        tgt = list(cur_lit)
        tgt[i] = lw(X)
        tgt[i] = [l for l in lw(X) if l[1] == 0] + [l for l in Ll[0] if l[1] == 0] +             [l for l in lw(X) if l[1] == 1] + [l for l in Ll[0] if l[1] == 1]
        for j in range(1, s):
            tgt[i + j] = Ll[j]
        last = Ll[s] + lw(Y) if s else None
        tgt[i + s] = [l for l in Ll[s] if l[1] == 0] + [l for l in lw(Y) if l[1] == 0] +             [l for l in Ll[s] if l[1] == 1] + [l for l in lw(Y) if l[1] == 1]
        for j in range(i, i + s + 1):
            ws, cur_lit = morph(cur_lit, j, tgt[j])
            words += ws
        # apply the rule
        t = len(Lr) - 1
        X0w = [l for l in lw(X) if l[1] == 0]
        X1w = [l for l in lw(X) if l[1] == 1]
        Y0w = [l for l in lw(Y) if l[1] == 0]
        Y1w = [l for l in lw(Y) if l[1] == 1]
        if t == 0:
            new = [X0w + [l for l in Lr[0] if l[1] == 0] + Y0w + X1w +
                   [l for l in Lr[0] if l[1] == 1] + Y1w]
        else:
            new = [X0w + [l for l in Lr[0] if l[1] == 0] + X1w + [l for l in Lr[0] if l[1] == 1]]
            new += [list(L) for L in Lr[1:t]]
            new.append([l for l in Lr[t] if l[1] == 0] + Y0w + [l for l in Lr[t] if l[1] == 1] + Y1w)
        cur_lit = cur_lit[:i] + new + cur_lit[i + s + 1:]
        words.append(join(cur_lit))
        lay = list(apply(tuple(lay), rule, i, rev))
        assert len(lay) == len(cur_lit)
        for j in range(len(cur_lit)):
            if cur_lit[j] != lw(lay[j]):
                ws, cur_lit = morph(cur_lit, j, lw(lay[j]))
                words += ws
    return words, lay


def sw(u):
    return [(g, 1 - j) for (g, j) in u]


def wpass(W, pre, u, post):
    """Words moving u from after W to before it, letter by letter."""
    out = []
    for k in range(1, len(u) + 1):
        out.append(pre + sw(u[:k]) + W + u[k:] + post)
    return out


def build2():
    import lib2
    E = lib2.build()
    rules = [Rule(nm, l, r) for nm, (l, r) in zip(list(E.names), E.table)]
    C = ('CZ', 0)
    W = qc.SWAP(0)
    # X on wire 1 passes CZ (search)
    start, goal = [C] + qc.X(1), [C]
    res = search(rules, reduce(start), reduce(goal), maxcz=6, maxdepth=9)
    fw, bw = res
    steps = [(ri, i, rev) for (_, ri, i, rev) in fw] + [(ri, i, rev) for (_, ri, i, rev) in bw]
    words, lay = replay(rules, start, steps)
    mu = lw(lay[0])
    assert lay[1:] == [IDL]
    words.append(mu + [C])
    E.chain('XP1', words)
    # X on wire 0 passes CZ: the mirror image
    X0 = qc.X(0)
    ch = [[C] + X0, W + W + [C] + X0, W + [C] + W + X0]
    ch += wpass(W, W + [C], X0, [])
    ch += [W + mu + [C] + W]
    ch += wpass(W, [], mu, [C] + W)
    ch += [sw(mu) + [C] + W + W, sw(mu) + [C]]
    E.chain('XP0', ch)
    return E


if __name__ == '__main__':
    E = build2()
    for nm, l, r, st in E.lemmas:
        print(nm, len(st), l, '->', r)
