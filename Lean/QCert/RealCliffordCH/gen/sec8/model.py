"""Parsed gates (figparse) as circuits of mc.py, and numerical checks.

`circ(N, gates, env)` expands the gate tuples of a parsed diagram into the primitive gate
list of mc.py (the conventions of Syntax.lean / Sec8/MC.lean); `env` gives the values of
the parameters (control colours such as 'beta', the sign 'a' of a '(-1)^a ZX' label).
"""
import itertools
import re

import numpy as np

import mc


def colour(c, env):
    if c == 'b':
        return True
    if c == 'w':
        return False
    return bool(env[c])


def ctl(N, ctrls, env):
    d = {w: colour(c, env) for w, c in ctrls.items()}
    return lambda j: d.get(j)


def white_x(N, ctrls, env):
    return [mc.xAt(N, w) for w, c in sorted(ctrls.items()) if not colour(c, env)]


def coloured(N, ctrls, env, g):
    xs = white_x(N, ctrls, env)
    return mc.drawn(*xs, g, *xs)


def zx_kind(lab, env):
    """'ZX', 'XZ', '(-1)aZX', ... -> 'zx' / 'xz'."""
    m = re.fullmatch(r'\(-1\)([a-z]+)(ZX|XZ)', lab)
    if m:
        neg = bool(env[m.group(1)])
        base = m.group(2)
        if neg:
            base = 'XZ' if base == 'ZX' else 'ZX'
        return base.lower()
    if lab in ('ZX', 'XZ'):
        return lab.lower()
    return None


def gate(N, g, env):
    k = g[0]
    if k == 'Z':
        return mc.zAt(N, g[1])
    if k == 'Zw':
        return mc.drawn(mc.xAt(N, g[1]), mc.zAt(N, g[1]), mc.xAt(N, g[1]))
    if k == 'H':
        return mc.hAt(N, g[1])
    if k == 'X':
        return mc.xAt(N, g[1])
    if k == 'SW':
        a, b = g[1], g[2]
        assert b == a + 1, g
        return mc.swAt(N, a)
    if k == 'PP':
        return mc.ppAt(N, g[1], g[2])
    if k == 'CZ':
        ws = sorted(g[1])
        assert len(ws) == 2, g
        return coloured(N, g[1], env, mc.czAt(N, ws[0], ws[1]))
    if k == 'BOX':
        return mc.mc(N, 'box', [g[1]], ctl(N, g[2], env))
    if k == 'CHB':
        return mc.mc(N, 'hg', [g[1], g[2]], ctl(N, g[3], env))
    if k == 'CU':
        lab, t, ctrls = g[1], g[2], g[3]
        zk = zx_kind(lab, env)
        if zk:
            return mc.mc(N, zk, [t], ctl(N, ctrls, env))
        if lab == 'H':
            if not ctrls:
                return mc.hAt(N, t)
            assert len(ctrls) == 1, g
            (c, _), = ctrls.items()
            return coloured(N, ctrls, env, mc.chAt(N, t, c))
        if lab == 'X':
            if not ctrls:
                return mc.xAt(N, t)
            assert len(ctrls) == 1, g
            (c, _), = ctrls.items()
            return coloured(N, ctrls, env, mc.drawn(mc.hAt(N, t), mc.czAt(N, min(t, c), max(t, c)), mc.hAt(N, t)))
    raise ValueError(f'cannot model {g}')


def circ(N, gates, env=None):
    env = env or {}
    out = []
    for g in gates:
        out += gate(N, g, env)
    return out


def params(gates):
    """The parameter names occurring in a gate list."""
    ps = set()
    for g in gates:
        for part in g[1:]:
            if isinstance(part, dict):
                ps |= {c for c in part.values() if c not in ('b', 'w')}
        if g[0] == 'CU':
            m = re.fullmatch(r'\(-1\)([a-z]+)(ZX|XZ)', g[1])
            if m:
                ps.add(m.group(1))
    return sorted(ps)


def envs(ps):
    for vals in itertools.product([0, 1], repeat=len(ps)):
        yield dict(zip(ps, vals))


def equal(N, gs1, gs2):
    """Do the two gate lists denote the same operator for every value of the parameters?"""
    ps = sorted(set(params(gs1)) | set(params(gs2)))
    for env in envs(ps):
        if not np.allclose(mc.mat(N, circ(N, gs1, env)), mc.mat(N, circ(N, gs2, env)), atol=1e-9):
            return False, env
    return True, None


# ----------------------------------------------------------------------------- letters

import letters as LT


def lcol(ctrls, env, g):
    ws = [w for w, c in sorted(ctrls.items()) if not colour(c, env)]
    return LT.colourW(ws, g)


def gate_letters(N, g, env):
    k = g[0]
    if k == 'Z':
        return LT.zAt(g[1])
    if k == 'Zw':
        return LT.xAt(g[1]) + LT.zAt(g[1]) + LT.xAt(g[1])
    if k == 'H':
        return LT.hAt(g[1])
    if k == 'X':
        return LT.xAt(g[1])
    if k == 'SW':
        assert g[2] == g[1] + 1, g
        return LT.swAt(g[1])
    if k == 'PP':
        return LT.ppAt(g[1], g[2])
    if k == 'CZ':
        ws = sorted(g[1])
        assert len(ws) == 2, g
        return lcol(g[1], env, LT.czAt(ws[0], ws[1]))
    if k == 'BOX':
        return LT.mcw(N, 'box', [g[1]], ctl(N, g[2], env))
    if k == 'CHB':
        return LT.mcw(N, 'hg', [g[1], g[2]], ctl(N, g[3], env))
    if k == 'CU':
        lab, t, ctrls = g[1], g[2], g[3]
        zk = zx_kind(lab, env)
        if zk:
            return LT.mcw(N, zk, [t], ctl(N, ctrls, env))
        if lab == 'H':
            if not ctrls:
                return LT.hAt(t)
            (c, _), = ctrls.items()
            return lcol(ctrls, env, LT.chAt(t, c))
        if lab == 'X':
            if not ctrls:
                return LT.xAt(t)
            (c, _), = ctrls.items()
            return lcol(ctrls, env, LT.hAt(t) + LT.czAt(min(t, c), max(t, c)) + LT.hAt(t))
    raise ValueError(f'cannot expand {g}')


def word(N, gates, env=None):
    env = env or {}
    out = []
    for g in gates:
        out += gate_letters(N, g, env)
    return out
