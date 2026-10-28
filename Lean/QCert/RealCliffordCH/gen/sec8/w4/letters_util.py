"""Letter words for tokens: within the span of their wires, and Definition 2.4 pieces.

`span_letters(N, t)`: a letter word with the semantics of t whose letters stay on the
wires min(t) .. max(t) (t moved down to its lowest wire, written there, shifted back).
`decompose(N, t)`: for a gadget token whose letters are `xs + net + canon + net^rev + xs`
(MC.mc: colourW of placeG of the canonical gate), the colour letters xs, the network net
and the canonical gate cut into pieces (letter block, token at the canonical position,
how to fold the block into the token).
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import letters as LT  # noqa: E402

import tok  # noqa: E402


def down(t, k):
    """t with every wire lowered by k."""
    if t[0] == 's':
        return ('s', t[1], t[2] - k)
    if t[0] == 'g':
        _, Kd, tg, cs = t
        return ('g', Kd, tuple(x - k for x in tg), tuple((w - k, c) for w, c in cs))
    _, m, w, ps = t
    return ('p', m, w, tuple(x - k for x in ps))


def span_letters(N, t):
    ws = tok.wires(t)
    lo, hi = min(ws), max(ws)
    if t[0] == 's':
        return [t[1:]]
    t2 = down(t, lo)
    L = tok.letters(hi - lo + 1, t2)
    return [(a, j + lo) for a, j in L]


def ctrl_info(N, t):
    _, Kd, tg, cs = t
    d = {}
    for w, c in cs:
        if w < N and w not in d:
            d[w] = c
    ctrls = [j for j in range(N) if j in d and j not in tg]
    whites = [j for j in range(N) if d.get(j) is False and j not in tg]
    return ctrls, whites


def tau_fold(solver):
    """Steps carrying [S0, S1, S0, C2, S0, S1, S0] to [CZ placed on 0, 3]."""
    C23 = tok.P(2, [('C', 0)], [2, 3])
    C13 = tok.P(2, [('C', 0)], [1, 3])
    C03 = tok.P(2, [('C', 0)], [0, 3])
    q = solver.window([('s', 'C', 2)], [C23])
    return [('sem', 3, 1, (C23,), q),
            ('swp', 2, 0, C23, C23, False),
            ('swp', 1, 1, C23, C13, False),
            ('swp', 0, 0, C13, C03, False)]


def fold_rw(t):
    """Fold a four-wire token's letters by its table entry."""
    def how(solver):
        k, L = solver.fold_entry(t)
        return [('rw', 0, k, False)]
    return how


def canon_pieces(Kd, k):
    """Definition 2.4 on at most four wires, as smaller gate factors."""
    if Kd == 'box' and k in (1, 2):
        letter = ('Z', 1) if k == 1 else ('C', 1)
        return [([letter], ('s',) + letter, None)]
    if Kd == 'hg' and k in (0, 1):
        letter = ('H', 1) if k == 0 else ('K', 1)
        return [([letter], ('s',) + letter, None)]
    if Kd in ('zx', 'xz') and k == 2:
        p1 = (LT.K0, ('s', 'K', 0), None)
        p2 = (LT.conj(LT.S0, LT.sh(LT.C0)), tok.P(2, LT.C0, [0, 2]), None)
        return [p1, p2, p1, p2] if Kd == 'zx' else [p2, p1, p2, p1]
    if Kd == 'box' and k == 3:
        B = LT.conj(LT.TAU02, LT.sh(LT.box(2)))
        return [(LT.zx(2), tok.G('zx', [0], [(1, 1), (2, 1)]), None),
                (B, tok.P(2, [('C', 0)], [0, 3]), tau_fold),
                (LT.xz(2), tok.G('xz', [0], [(1, 1), (2, 1)]), None),
                (B, tok.P(2, [('C', 0)], [0, 3]), tau_fold)]
    if Kd in ('zx', 'xz') and k == 3:
        bx = tok.G('box', [1], [(0, 1), (2, 1), (3, 1)])
        cb = LT.conj(LT.S0, LT.box(3))
        p1 = (LT.K0, ('s', 'K', 0), None)
        p2 = (cb, bx, fold_rw(bx))
        return [p1, p2, p1, p2] if Kd == 'zx' else [p2, p1, p2, p1]
    if Kd == 'hg' and k == 2:
        pp = tok.P(2, LT.PP0, [0, 1])
        bx = tok.G('box', [0], [(1, 1), (2, 1), (3, 1)])
        return [(LT.PP0, pp, None), (LT.box(3), bx, fold_rw(bx)), (LT.PP0, pp, None)]
    return None


def decompose(N, t):
    if t[0] != 'g':
        return None
    _, Kd, tg, cs = t
    ctrls, whites = ctrl_info(N, t)
    pieces = canon_pieces(Kd, len(ctrls))
    if pieces is None:
        return None
    xs = [l for w in whites for l in LT.xAt(w)]
    net = LT.netL(list(tg) + ctrls)
    flat = xs + net + [l for p in pieces for l in p[0]] + list(reversed(net)) + xs
    assert [tuple(l) for l in flat] == list(tok.letters(N, t)), t
    return ([('s',) + tuple(l) for l in xs], [('s',) + tuple(l) for l in net],
            [([tuple(l) for l in p[0]], p[1], p[2]) for p in pieces])
