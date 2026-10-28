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


X0 = [('H', 0), ('Z', 0), ('H', 0)]


def X(w):
    return [P(1, X0, [w])]


def colour(c, env):
    return model.colour(c, env)


def local_x(ctrls, env, local):
    """X letters on the local wires of the white controls (local: wire -> local wire)."""
    out = []
    for w, c in sorted(ctrls.items()):
        if not colour(c, env):
            out += [(k, j + local[w]) for k, j in X0]
    return out


def two(core, a, b, ctrls, env):
    """A two-wire gate with its local wires 0, 1 on the wires a, b, coloured."""
    xs = local_x(ctrls, env, {a: 0, b: 1})
    if not xs and b == a + 1 and len(core) == 1:
        return [S(core[0][0], a)]
    if not xs and b == a + 1:
        return [S(k, j + a) for k, j in core] if False else [P(2, core, [a, b])]
    return [P(2, xs + core + xs, [a, b])]


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
        return [P(1, X0 + [('Z', 0)] + X0, [g[1]])]
    if k == 'SW':
        assert g[2] == g[1] + 1, g
        return [S('S', g[1])]
    if k == 'PP':
        return [P(2, PP0, [g[1], g[2]])]
    if k == 'CZ':
        ws = sorted(g[1])
        assert len(ws) == 2, g
        return two([('C', 0)], ws[0], ws[1], g[1], env)
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
            return two([('K', 0)], t, c, ctrls, env)
        if lab == 'X':
            if not ctrls:
                return X(t)
            (c, _), = ctrls.items()
            return two([('H', 0), ('C', 0), ('H', 0)], t, c, ctrls, env)
    raise ValueError(f'cannot convert {g}')


def word(N, gates, env=None):
    out = []
    for g in gates:
        out += gate_tokens(N, g, env)
    return out
