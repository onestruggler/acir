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



def split_raw(w):
    layers, cur = [], []
    for l in w:
        if l[0] == 'CZ':
            layers.append(cur)
            cur = []
        else:
            cur.append(l)
    layers.append(cur)
    return layers


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
    pre = list(layers)
    pre[j] = o0 + [l for l in old if l[1] == 1]
    mid = list(layers)
    mid[j] = n0 + [l for l in old if l[1] == 1]
    out = [join(pre), join(mid)]
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
        # reorder (commuting letters) so that the rule's letters are adjacent
        cur_lit = list(cur_lit)
        Rl = split_raw(lwd)
        cur_lit[i] = lw(X) + Rl[0]
        cur_lit[i + s] = Rl[s] + lw(Y)
        words.append(join(cur_lit))
        # apply the rule
        t = len(Lr) - 1
        X0w = [l for l in lw(X) if l[1] == 0]
        X1w = [l for l in lw(X) if l[1] == 1]
        Y0w = [l for l in lw(Y) if l[1] == 0]
        Y1w = [l for l in lw(Y) if l[1] == 1]
        Rr = split_raw(rwd)
        if t == 0:
            new = [lw(X) + Rr[0] + lw(Y)]
        else:
            new = [lw(X) + Rr[0]] + [list(L) for L in Rr[1:t]] + [Rr[t] + lw(Y)]
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
    return [(g, 1 - j) if g != 'CZ' else (g, j) for (g, j) in u]


def wpass(W, pre, u, post):
    """Words moving u from after W to before it, letter by letter (CZ by
    (C12), one-wire letters by the swap lemmas)."""
    out = []
    for k in range(1, len(u) + 1):
        out.append(pre + sw(u[:k]) + W + u[k:] + post)
    return out


def mirror(E, name, l, r):
    """The lemma sw(l) = sw(r) from l = r (a table entry), by the swap."""
    W = qc.SWAP(0)
    L, R = sw(l), sw(r)
    ch = [L, W + W + L, W + l + W]
    ch = [L, W + W + L] + wpass(W, W, L, [])
    ch = [L, W + W + L] + [W + x for x in wpass(W, [], L, [])]
    ch.append(W + r + W)
    ch += wpass(W, [], r, W)
    ch.append(R + W + W)
    ch.append(R)
    E.chain(name, ch)


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


def derive(E, name, start, goal_layers_tail, maxcz=6, maxdepth=8):
    """Derive start = mu ; goal (goal given by its layers after the first,
    which is free) with the current table; returns the lemma index."""
    rules = [Rule(nm, l, r) for nm, (l, r) in zip(list(E.names), E.table)]
    goal = (IDL,) + tuple(goal_layers_tail)
    res = search(rules, reduce(start), goal, maxcz=maxcz, maxdepth=maxdepth)
    if res is None:
        return None
    fw, bw = res
    steps = [(ri, i, rev) for (_, ri, i, rev) in fw] + [(ri, i, rev) for (_, ri, i, rev) in bw]
    words, lay = replay(rules, start, steps)
    return words, lay


STAB_FACTS = []


def stab_facts(E):
    T = cosets.Table(2, [('H', 0), ('S', 0), ('H', 1), ('S', 1), ('CZ', 0)],
                     [('H', 0), ('S', 0), ('H', 1), ('S', 1)])
    for c, ms in STAB.items():
        N = T.N[c]
        tail = reduce(N)[1:]
        for m in ms:
            r = derive(E, 'stab', N + m, tail)
            if r is None:
                print('NOT FOUND', c, m)
                continue
            words, lay = r
            mu = lw(lay[0])
            Nl = split_raw(N)
            fin = [mu + Nl[0]] + Nl[1:]
            words.append(join(fin))
            nm = 'ST%d_%d' % (c, len(STAB_FACTS))
            E.chain(nm, words)
            STAB_FACTS.append((c, m, mu))
            print(nm, c, m, 'steps', len(E.lemmas[-1][3]))


STAB = {
    1: [[('S', 0)], [('S', 1)], [('H', 0), ('H', 0), ('H', 1), ('H', 1)],
        [('H', 0)] * 3 + [('S', 0), ('H', 0), ('S', 0), ('H', 0)],
        [('H', 0), ('H', 0), ('H', 1), ('S', 1), ('H', 1), ('S', 1), ('H', 1)]],
    13: [[('S', 0), ('H', 0), ('S', 0)], [('S', 1), ('H', 1), ('S', 1)],
         [('H', 0), ('H', 0), ('H', 1), ('H', 1)]],
    27: [[('H', 0), ('H', 1)], [('H', 0), ('S', 0), ('S', 1), ('H', 1)],
         [('S', 0), ('H', 0), ('H', 1), ('S', 1)]],
    69: [[('H', 0)], [('S', 0)], [('H', 1)], [('S', 1)]],
}




# ---- stabiliser facts by passing through CZ and SWAP --------------------

LOC = [('H', 0), ('S', 0), ('H', 1), ('S', 1)]


def islocal2(w):
    k = cliff.key(w, 2)
    return (k[0][1][1] == 0 and k[0][2][1] == 0 and k[1][1][1] == 0 and k[1][2][1] == 0 and
            k[2][1][0] == 0 and k[2][2][0] == 0 and k[3][1][0] == 0 and k[3][2][0] == 0)


def wires_split(w):
    return [l for l in w if l[1] == 0], [l for l in w if l[1] == 1]


def rewrite_local(pre, old, new, post):
    """Free steps rewriting a local word old into new (same element)."""
    o0, o1 = wires_split(old)
    n0, n1 = wires_split(new)
    return [pre + o0 + o1 + post, pre + n0 + o1 + post, pre + n0 + n1 + post, pre + new + post]


class Passer:
    """Moves local words through CZ (P-elements) using the lemmas
    [CZ] g = mu_g [CZ] for generators g of P."""

    def __init__(self, E, gens):
        self.E = E
        self.gens = gens            # list of (g word, mu word)
        lk = [cliff.key(g, 2) for g, _ in gens]
        start = cliff.ident(2)
        seen = {start: []}
        q = [start]
        while q:
            nq = []
            for k in q:
                for i, g in enumerate(lk):
                    k2 = cliff.compose(k, g)
                    if k2 not in seen:
                        seen[k2] = seen[k] + [i]
                        nq.append(k2)
            q = nq
        self.words = seen

    def through(self, pre, m, post):
        """Chain from pre + [CZ] + m + post to pre + mu + [CZ] + post."""
        C = ('CZ', 0)
        idx = self.words[cliff.key(m, 2)]
        G = []
        for i in idx:
            G += self.gens[i][0]
        ch = rewrite_local(pre + [C], m, G, post)
        mus = []
        rest = list(idx)
        while rest:
            i = rest.pop(0)
            mus += self.gens[i][1]
            tail = []
            for j in rest:
                tail += self.gens[j][0]
            ch.append(pre + mus + [C] + tail + post)
        mu = mus
        return ch, mu


def build_stab():
    E = build2()
    C = ('CZ', 0)
    W = qc.SWAP(0)
    h = [('H', 0), ('H', 1)]
    hi = [('H', 0)] * 3 + [('H', 1)] * 3
    # D1: the generators of P pass CZ
    gens = []
    for c, m in [(None, [('S', 0)]), (None, [('S', 1)]),
                 (None, [('H', 0), ('H', 0), ('H', 1), ('H', 1)]),
                 (None, qc.X(0)), (None, qc.X(1))]:
        r = derive(E, 'p', [C] + m, reduce([C])[1:])
        words, lay = r
        mu = lw(lay[0])
        words.append(mu + [C])
        E.chain('P%d' % len(gens), words)
        gens.append((m, mu))
    Pa = Passer(E, gens)
    out = {}
    # D1 stabiliser facts
    for m in STAB[1]:
        ch, mu = Pa.through([], m, [])
        E.chain('ST1', ch)
        out.setdefault(1, []).append((m, mu))
    # CZ h CZ = h^-1 W CZ^2 h^-1
    N13 = [C] + h + [C]
    H04, H14 = [('H', 0)] * 4, [('H', 1)] * 4
    E.chain('N13W', [N13, N13 + H04, N13 + H04 + H14, N13 + h + hi, N13 + h + [C] * 3 + hi,
                     H04 + N13 + h + [C] * 3 + hi, H04 + H14 + N13 + h + [C] * 3 + hi,
                     hi + W + [C, C] + hi])
    l13, r13 = E.table[E.names['C13']]
    mirror(E, 'M13', l13, r13)
    l14, r14 = E.table[E.names['C14']]
    mirror(E, 'M14', l14, r14)
    # D13: N13 = hi W CZ CZ hi, through which the stabiliser passes
    for m in STAB[13]:
        p = hi + m + h            # hi m = p hi
        ch = [N13 + m, hi + W + [C, C] + hi + m]
        ch += rewrite_local(hi + W + [C, C], hi + m, p + hi, [])
        c1, mu1 = Pa.through(hi + W + [C], p, hi)
        c2, mu2 = Pa.through(hi + W, mu1, [C] + hi)
        ch += c1 + c2
        ch += wpass(W, hi, mu2, [C, C] + hi)
        mu3 = hi + sw(mu2) + h
        ch += rewrite_local([], hi + sw(mu2), mu3 + hi, W + [C, C] + hi)
        ch.append(mu3 + N13)
        E.chain('ST13', ch)
        out.setdefault(13, []).append((m, mu3))
    # D69: N69 = hi W
    N69 = [C] + h + [C] + h + [C]
    E.chain('N69W', [N69, H04 + N69, H04 + H14 + N69, hi + W])
    for m in STAB[69]:
        ch = [N69 + m, hi + W + m] + wpass(W, hi, m, [])
        mu = hi + sw(m) + h
        ch += rewrite_local([], hi + sw(m), mu + hi, W)
        ch.append(mu + N69)
        E.chain('ST69', ch)
        out.setdefault(69, []).append((m, mu))
    return E, Pa, out


if __name__ == '__main__':
    E, Pa, out = build_stab()
    print(len(E.lemmas), 'lemmas')


# ---- P-canonical search -------------------------------------------------

class PCanon:
    """Two-wire words modulo CZ-passing: every inner layer reduced to a
    fixed representative of its coset P q (P the local elements passing
    CZ), the rest pushed to the front."""

    def __init__(self, E, Pa):
        self.E, self.Pa = E, Pa
        C = ('CZ', 0)
        self.T = cosets.Table(2, LOC + [C], LOC)
        self.reps = {}
        for i0 in range(216):
            for i1 in range(216):
                c = self.coset((i0, i1))
                if c not in self.reps:
                    self.reps[c] = (i0, i1)
        self.mu = {}

    def coset(self, l):
        C = ('CZ', 0)
        return self.T.idx[cosets.coset_key(cliff.key([C] + word_of_layer(l), 2), 2)]

    def split(self, l):
        q = self.reps[self.coset(l)]
        return mul(l, inv(q)), q

    def mu_of(self, p):
        C = ('CZ', 0)
        if p not in self.mu:
            k = cliff.key([C] + word_of_layer(p) + [C, C], 2)
            a = ((k[0][0], (k[0][1][0],), (k[0][2][0],)), (k[1][0], (k[1][1][0],), (k[1][2][0],)))
            b = ((k[2][0], (k[2][1][1],), (k[2][2][1],)), (k[3][0], (k[3][1][1],), (k[3][2][1],)))
            self.mu[p] = (IDX[a], IDX[b])
        return self.mu[p]

    def canon(self, state, keep0=False):
        st = list(state)
        for i in range(len(st) - 1, 0, -1):
            p, q = self.split(st[i])
            st[i] = q
            st[i - 1] = mul(st[i - 1], self.mu_of(p))
        if not keep0:
            st[0] = IDL
        return tuple(st)

    def chain(self, lit, lay):
        """Words canonicalising the explicit word with literal layers lit
        (elements lay); returns the words and the new literal layers."""
        lit, lay = [list(L) for L in lit], list(lay)
        words = []
        for i in range(len(lay) - 1, 0, -1):
            p, q = self.split(lay[i])
            if p == IDL:
                if lit[i] != lw(q):
                    ws, lit = morph(lit, i, lw(q))
                    words += ws
                continue
            pre = join(lit[:i])
            post = [('CZ', 0)] + join(lit[i + 1:]) if i + 1 < len(lit) else []
            words += rewrite_local(pre + [('CZ', 0)], lit[i], lw(p) + lw(q), post)
            ch, muw = self.Pa.through(pre, lw(p), lw(q) + post)
            words += ch
            lit[i - 1] = lit[i - 1] + muw
            lit[i] = lw(q)
            lay[i] = q
            lay[i - 1] = mul(lay[i - 1], reduce(muw)[0])
        if lit[0] != lw(lay[0]):
            ws, lit = morph(lit, 0, lw(lay[0]))
            words += ws
        return words, lit, lay


def search_pc(PC, rules, start, goal, maxd=8, maxlay=6):
    """Forward moves from both ends to a common canonical state."""
    fw = {start: None}
    bw = {goal: None}
    fq, bq = [start], [goal]
    for d in range(maxd):
        for seen, q, other in ((fw, fq, bw), (bw, bq, fw)):
            nq = []
            for st in q:
                for ri, rule in enumerate(rules):
                    for rev in (False, True):
                        for i in range(len(st) - 1):
                            ns = apply(st, rule, i, rev)
                            if ns is None or len(ns) > maxlay:
                                continue
                            ns = PC.canon(ns)
                            if ns in seen:
                                continue
                            seen[ns] = (st, ri, i, rev)
                            if ns in other:
                                return trail(fw, ns), trail(bw, ns)
                            nq.append(ns)
            q[:] = nq
    return None


def trail(seen, s):
    out = []
    while seen[s] is not None:
        st, ri, i, rev = seen[s]
        out.append((ri, i, rev))
        s = st
    return out[::-1]


def replay_pc(PC, rules, start, steps):
    """Explicit words: canonicalise, then each rule followed by a
    canonicalisation."""
    lay = list(reduce(start))
    lit = split_layers(start)
    words = [list(start)]
    ws, lit, lay = PC.chain(lit, lay)
    words += ws
    for (ri, i, rev) in steps:
        w2, lay2 = replay(rules, join(lit), [(ri, i, rev)])
        words += w2[1:]
        lay = lay2
        lit = split_layers(w2[-1])
        ws, lit, lay = PC.chain(lit, lay)
        words += ws
    return words, lit, lay


def derive_pc(E, PC, start, goal_word):
    """Words from start to mu ; goal_word; returns them and mu."""
    rules = [Rule(str(i), l, r) for i, (l, r) in enumerate(E.table)
             if not (len(reduce(l)) == 2 and len(reduce(r)) == 2)]
    res = search_pc(PC, rules, PC.canon(reduce(start)), PC.canon(reduce(goal_word)))
    if res is None:
        return None
    sf, gf = res
    sw_, slit, slay = replay_pc(PC, rules, start, sf)
    gw_, glit, glay = replay_pc(PC, rules, goal_word, gf)
    assert tuple(slay[1:]) == tuple(glay[1:]) and slit[1:] == glit[1:]
    pre = mul(slay[0], inv(glay[0]))
    ws, slit = morph(slit, 0, lw(pre) + lw(glay[0]))
    words = sw_ + ws + [lw(pre) + g for g in gw_[::-1]]
    return words, lw(pre)


def d27_facts(E, Pa, out):
    PC = PCanon(E, Pa)
    C = ('CZ', 0)
    T = PC.T
    N = T.N[27]
    for m in STAB[27]:
        r = derive_pc(E, PC, N + m, N)
        words, mu = r
        E.chain('ST27', words)
        out.setdefault(27, []).append((m, mu))


if __name__ == '__main__':
    E, Pa, out = build_stab()
    d27_facts(E, Pa, out)
    print(len(E.lemmas), 'lemmas', {c: len(v) for c, v in out.items()})
