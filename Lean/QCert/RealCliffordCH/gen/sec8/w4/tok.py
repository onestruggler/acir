"""Tokens of Sec8/D/WEng.lean (`WE.Tk`) and a model of its engine.

A token is a tuple:
    ('s', kind, j)              a letter of EngineN (`Tk.s (L.kind j)`)
    ('g', Kd, tg, cs)           `mc N Kd tg (SE.ctl N cs false)`; tg a tuple of wires, cs a
                                tuple of (wire, colour) pairs (True black)
    ('p', m, w, ps)             the m-wire letter word w (a tuple of letters) placed on the
                                wires ps (`placeG`)
`letters(N, t)` is the letter word of `Tk.circ N t` on the nose (MC.lean's mc, placeG,
colourW, mirrored by letters.py), `mat` its matrix; `ok`, `avoids`, `drop` mirror the Lean
functions, and `Engine.apply_step` mirrors `WE.applyStep` (the semantic check numerically).
"""
import os
import sys
from functools import lru_cache

import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import letters as LT  # noqa: E402

CANON = {'box': LT.box, 'zx': LT.zx, 'xz': LT.xz, 'hg': LT.mch}
SP = {'box': 1, 'zx': 1, 'xz': 1, 'hg': 2}


def S(kind, j):
    return ('s', kind, j)


def G(Kd, tg, cs):
    return ('g', Kd, tuple(tg), tuple(sorted(((w, bool(c)) for w, c in cs), reverse=True)))


def P(m, w, ps):
    return ('p', m, tuple(tuple(x) for x in w), tuple(ps))


def lo(l):
    return l[1]


def wd(l):
    return 1 if l[0] in 'HZ' else 2


@lru_cache(None)
def letters(N, t):
    if t[0] == 's':
        return ((t[1], t[2]),)
    if t[0] == 'g':
        _, Kd, tg, cs = t
        d = {}
        for w, c in cs:
            if w < N and w not in d:
                d[w] = c
        ctrls = [j for j in range(N) if j in d and j not in tg]
        whites = [j for j in range(N) if d.get(j) is False and j not in tg]
        g = CANON[Kd](len(ctrls))
        return tuple(tuple(x) for x in LT.colourW(whites, LT.placeG(g, list(tg) + ctrls)))
    if t[0] == 'p':
        _, m, w, ps = t
        return tuple(tuple(x) for x in LT.placeG(list(w), list(ps)))
    raise ValueError(t)


@lru_cache(None)
def mat(N, t):
    return LT.mat(N, list(letters(N, t)))


def wmat(N, ts):
    M = np.eye(2 ** N)
    for t in ts:
        M = mat(N, t) @ M
    return M


def weq(N, a, b):
    return np.allclose(wmat(N, a), wmat(N, b), atol=1e-9)


def wires(t):
    if t[0] == 's':
        return set(range(t[2], t[2] + (1 if t[1] in 'HZ' else 2)))
    if t[0] == 'g':
        return set(t[2]) | {w for w, _ in t[3]}
    return set(t[3])


def ok(N, t):
    if t[0] == 's':
        return t[2] + (1 if t[1] in 'HZ' else 2) <= N
    if t[0] == 'g':
        _, Kd, tg, cs = t
        return len(set(tg)) == len(tg) and all(x < N for x in tg) and len(tg) == SP[Kd]
    _, m, w, ps = t
    return (len(set(ps)) == len(ps) and all(x < N for x in ps) and len(ps) == m
            and all(lo(x) + wd(x) <= m for x in w))


def avoids(q, t):
    if t[0] == 's':
        j, k = t[2], (1 if t[1] in 'HZ' else 2)
        return j + k <= q or q < j
    if t[0] == 'g':
        return q not in t[2] and all(w != q for w, _ in t[3])
    return q not in t[3]


def dropW(q, j):
    return j if j < q else j - 1


def drop(q, t):
    if t[0] == 's':
        return ('s', t[1], t[2] - 1) if q < t[2] else t
    if t[0] == 'g':
        _, Kd, tg, cs = t
        return ('g', Kd, tuple(dropW(q, x) for x in tg), tuple((dropW(q, w), c) for w, c in cs))
    _, m, w, ps = t
    return ('p', m, w, tuple(dropW(q, x) for x in ps))


def disj(x, y):
    """Two letters (kind, j) on disjoint wires."""
    a = set(range(x[1], x[1] + (1 if x[0] in 'HZ' else 2)))
    b = set(range(y[1], y[1] + (1 if y[0] in 'HZ' else 2)))
    return not (a & b)


def sem_ok(M, q, a, b):
    """WE.semOK on M + 1 wires (numerically)."""
    if q > M:
        return False
    if not all(ok(M + 1, x) and avoids(q, x) for x in a + b):
        return False
    da = [drop(q, x) for x in a]
    db = [drop(q, x) for x in b]
    if not all(ok(M, x) for x in da + db):
        return False
    return weq(M, da, db)


def tau(j, q):
    return j + 1 if q == j else (j if q == j + 1 else q)


def relabel(t, j):
    """The token conjugated by the swap of wires j, j + 1 (for 'p' and 'g' tokens)."""
    if t[0] == 'p':
        _, m, w, ps = t
        return ('p', m, w, tuple(tau(j, x) for x in ps))
    if t[0] == 'g':
        _, Kd, tg, cs = t
        return ('g', Kd, tuple(tau(j, x) for x in tg),
                tuple(sorted(((tau(j, w), c) for w, c in cs), reverse=True)))
    raise ValueError(t)


def ctrl_wires(N, t):
    _, Kd, tg, cs = t
    d = {}
    for w, c in cs:
        if w < N and w not in d:
            d[w] = c
    return [x for x in range(N) if x in d and x not in tg]


def swp_ok(N, j, a, b):
    """WE.swpOK."""
    if j + 2 > N or a[0] != b[0] or a[0] == 's':
        return False
    if a[0] == 'p':
        return a[1] == b[1] and a[2] == b[2] and b[3] == tuple(tau(j, x) for x in a[3]) and ok(N, a)
    _, Kd, tg, cs = a
    if b[1] != Kd or b[2] != tuple(tau(j, x) for x in tg) or not ok(N, a):
        return False
    da, db = {}, {}
    for w, c in cs:
        da.setdefault(w, c)
    for w, c in b[3]:
        db.setdefault(w, c)
    if any(db.get(i) != da.get(tau(j, i)) for i in range(N)):
        return False
    cw = ctrl_wires(N, a)
    return not (j in cw and j + 1 in cw)


class Engine:
    def __init__(self, M, table):
        self.M = M              # M + 1 wires
        self.table = table      # list of (lhs, rhs) token lists

    def apply_step(self, cur, s):
        if s[0] == 'rw':
            _, i, k, d = s
            l, r = self.table[k]
            if d:
                l, r = r, l
            if list(cur[i:i + len(l)]) == list(l):
                return list(cur[:i]) + list(r) + list(cur[i + len(l):])
            return None
        if s[0] == 'sw':
            i = s[1]
            if i + 2 <= len(cur) and cur[i][0] == 's' and cur[i + 1][0] == 's' and disj(cur[i][1:], cur[i + 1][1:]):
                return list(cur[:i]) + [cur[i + 1], cur[i]] + list(cur[i + 2:])
            return None
        if s[0] == 'sem':
            _, i, n, r, q = s
            if i + n <= len(cur) and sem_ok(self.M, q, list(cur[i:i + n]), list(r)):
                return list(cur[:i]) + list(r) + list(cur[i + n:])
            return None
        if s[0] == 'swp':
            _, i, j, a, b, d = s
            if not swp_ok(self.M + 1, j, a, b):
                return None
            sj = ('s', 'S', j)
            if d:
                if i < len(cur) and cur[i] == b:
                    return list(cur[:i]) + [sj, a, sj] + list(cur[i + 1:])
                return None
            if list(cur[i:i + 3]) == [sj, a, sj]:
                return list(cur[:i]) + [b] + list(cur[i + 3:])
            return None
        raise ValueError(s)

    def run(self, w, steps):
        cur = list(w)
        for k, s in enumerate(steps):
            nxt = self.apply_step(cur, s)
            if nxt is None:
                return None, (k, s)
            cur = nxt
        return cur, None


# ----------------------------------------------------------------------------- Lean output

def lean_letter(l):
    return f'L.{l[0]} {l[1]}'


def lean_tok(t):
    if t[0] == 's':
        return f't{t[1]} {t[2]}'
    if t[0] == 'g':
        _, Kd, tg, cs = t
        tgs = '[' + ', '.join(map(str, tg)) + ']'
        css = '[' + ', '.join(f'({w}, {"true" if c else "false"})' for w, c in cs) + ']'
        return f'tg .{Kd} {tgs} {css}'
    _, m, w, ps = t
    ws = '[' + ', '.join(lean_letter(l) for l in w) + ']'
    pss = '[' + ', '.join(map(str, ps)) + ']'
    return f'tp {m} {ws} {pss}'


def lean_word(ts):
    return '[' + ', '.join(lean_tok(t) for t in ts) + ']'


def lean_step(s):
    if s[0] == 'rw':
        return f'.rw {s[1]} {s[2]} {"true" if s[3] else "false"}'
    if s[0] == 'sw':
        return f'.sw {s[1]}'
    if s[0] == 'swp':
        return f'.swp {s[1]} {s[2]} ({lean_tok(s[3])}) ({lean_tok(s[4])}) {"true" if s[5] else "false"}'
    return f'.sem {s[1]} {s[2]} {lean_word(s[3])} {s[4]}'
