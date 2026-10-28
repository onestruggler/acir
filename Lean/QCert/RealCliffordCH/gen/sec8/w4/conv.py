"""Parsed gates (figparse) as tokens of WEng.

`gate_tokens(N, g, env)`: the token word of a parsed gate; small gates on adjacent wires
are letters, on other wires placed words (`P`), multi-controlled gates `mc` tokens (`G`).
A white control of a small gate is X (H Z H) on its wire on both sides; the colours of a
multi-controlled gate are its own.
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import model  # noqa: E402
import letters as LT  # noqa: E402

from tok import S, G, P  # noqa: E402

PP0 = [tuple(x) for x in LT.PP0]


def X(w):
    return [S('H', w), S('Z', w), S('H', w)]


def colour(c, env):
    return model.colour(c, env)


def xs_white(ctrls, env):
    out = []
    for w, c in sorted(ctrls.items()):
        if not colour(c, env):
            out += X(w)
    return out


def cz(a, b):
    lo, hi = min(a, b), max(a, b)
    if hi == lo + 1:
        return [S('C', lo)]
    return [P(2, [('C', 0)], [lo, hi])]


def ch(t, c):
    if c == t + 1:
        return [S('K', t)]
    return [P(2, [('K', 0)], [t, c])]


def pp(a, b):
    if b == a + 1:
        return [S(k, j + a) for k, j in PP0]
    return [P(2, PP0, [a, b])]


def gate_tokens(N, g, env=None):
    env = env or {}
    k = g[0]
    if k == 'Z':
        return [S('Z', g[1])]
    if k == 'H':
        return [S('H', g[1])]
    if k == 'X':
        return X(g[1])
    if k == 'Zw':
        return X(g[1]) + [S('Z', g[1])] + X(g[1])
    if k == 'SW':
        assert g[2] == g[1] + 1, g
        return [S('S', g[1])]
    if k == 'PP':
        return pp(g[1], g[2])
    if k == 'CZ':
        ws = sorted(g[1])
        assert len(ws) == 2, g
        xs = xs_white(g[1], env)
        return xs + cz(ws[0], ws[1]) + xs
    if k == 'BOX':
        return [G('box', [g[1]], [(w, colour(c, env)) for w, c in g[2].items()])]
    if k == 'CHB':
        return [G('hg', [g[1], g[2]], [(w, colour(c, env)) for w, c in g[3].items()])]
    if k == 'CU':
        lab, t, ctrls = g[1], g[2], g[3]
        zk = model.zx_kind(lab, env)
        if zk:
            return [G(zk, [t], [(w, colour(c, env)) for w, c in ctrls.items()])]
        if lab == 'H':
            if not ctrls:
                return [S('H', t)]
            (c, _), = ctrls.items()
            xs = xs_white(ctrls, env)
            return xs + ch(t, c) + xs
        if lab == 'X':
            if not ctrls:
                return X(t)
            (c, _), = ctrls.items()
            xs = xs_white(ctrls, env)
            return xs + [S('H', t)] + cz(t, c) + [S('H', t)] + xs
    raise ValueError(f'cannot convert {g}')


def word(N, gates, env=None):
    out = []
    for g in gates:
        out += gate_tokens(N, g, env)
    return out
